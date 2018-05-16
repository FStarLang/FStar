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
  | Unascribe 
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
  
type steps = step Prims.list
let cases :
  'Auu____248 'Auu____249 .
    ('Auu____248 -> 'Auu____249) ->
      'Auu____249 ->
        'Auu____248 FStar_Pervasives_Native.option -> 'Auu____249
  =
  fun f  ->
    fun d  ->
      fun uu___238_269  ->
        match uu___238_269 with
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
  weakly_reduce_scrutinee: Prims.bool }
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
      let add_opt x uu___239_1503 =
        match uu___239_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___258_1523 = fs  in
          {
            beta = true;
            iota = (uu___258_1523.iota);
            zeta = (uu___258_1523.zeta);
            weak = (uu___258_1523.weak);
            hnf = (uu___258_1523.hnf);
            primops = (uu___258_1523.primops);
            do_not_unfold_pure_lets = (uu___258_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___258_1523.unfold_until);
            unfold_only = (uu___258_1523.unfold_only);
            unfold_fully = (uu___258_1523.unfold_fully);
            unfold_attr = (uu___258_1523.unfold_attr);
            unfold_tac = (uu___258_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___258_1523.pure_subterms_within_computations);
            simplify = (uu___258_1523.simplify);
            erase_universes = (uu___258_1523.erase_universes);
            allow_unbound_universes = (uu___258_1523.allow_unbound_universes);
            reify_ = (uu___258_1523.reify_);
            compress_uvars = (uu___258_1523.compress_uvars);
            no_full_norm = (uu___258_1523.no_full_norm);
            check_no_uvars = (uu___258_1523.check_no_uvars);
            unmeta = (uu___258_1523.unmeta);
            unascribe = (uu___258_1523.unascribe);
            in_full_norm_request = (uu___258_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___258_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___259_1524 = fs  in
          {
            beta = (uu___259_1524.beta);
            iota = true;
            zeta = (uu___259_1524.zeta);
            weak = (uu___259_1524.weak);
            hnf = (uu___259_1524.hnf);
            primops = (uu___259_1524.primops);
            do_not_unfold_pure_lets = (uu___259_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___259_1524.unfold_until);
            unfold_only = (uu___259_1524.unfold_only);
            unfold_fully = (uu___259_1524.unfold_fully);
            unfold_attr = (uu___259_1524.unfold_attr);
            unfold_tac = (uu___259_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___259_1524.pure_subterms_within_computations);
            simplify = (uu___259_1524.simplify);
            erase_universes = (uu___259_1524.erase_universes);
            allow_unbound_universes = (uu___259_1524.allow_unbound_universes);
            reify_ = (uu___259_1524.reify_);
            compress_uvars = (uu___259_1524.compress_uvars);
            no_full_norm = (uu___259_1524.no_full_norm);
            check_no_uvars = (uu___259_1524.check_no_uvars);
            unmeta = (uu___259_1524.unmeta);
            unascribe = (uu___259_1524.unascribe);
            in_full_norm_request = (uu___259_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___259_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___260_1525 = fs  in
          {
            beta = (uu___260_1525.beta);
            iota = (uu___260_1525.iota);
            zeta = true;
            weak = (uu___260_1525.weak);
            hnf = (uu___260_1525.hnf);
            primops = (uu___260_1525.primops);
            do_not_unfold_pure_lets = (uu___260_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___260_1525.unfold_until);
            unfold_only = (uu___260_1525.unfold_only);
            unfold_fully = (uu___260_1525.unfold_fully);
            unfold_attr = (uu___260_1525.unfold_attr);
            unfold_tac = (uu___260_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___260_1525.pure_subterms_within_computations);
            simplify = (uu___260_1525.simplify);
            erase_universes = (uu___260_1525.erase_universes);
            allow_unbound_universes = (uu___260_1525.allow_unbound_universes);
            reify_ = (uu___260_1525.reify_);
            compress_uvars = (uu___260_1525.compress_uvars);
            no_full_norm = (uu___260_1525.no_full_norm);
            check_no_uvars = (uu___260_1525.check_no_uvars);
            unmeta = (uu___260_1525.unmeta);
            unascribe = (uu___260_1525.unascribe);
            in_full_norm_request = (uu___260_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___260_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___261_1526 = fs  in
          {
            beta = false;
            iota = (uu___261_1526.iota);
            zeta = (uu___261_1526.zeta);
            weak = (uu___261_1526.weak);
            hnf = (uu___261_1526.hnf);
            primops = (uu___261_1526.primops);
            do_not_unfold_pure_lets = (uu___261_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___261_1526.unfold_until);
            unfold_only = (uu___261_1526.unfold_only);
            unfold_fully = (uu___261_1526.unfold_fully);
            unfold_attr = (uu___261_1526.unfold_attr);
            unfold_tac = (uu___261_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___261_1526.pure_subterms_within_computations);
            simplify = (uu___261_1526.simplify);
            erase_universes = (uu___261_1526.erase_universes);
            allow_unbound_universes = (uu___261_1526.allow_unbound_universes);
            reify_ = (uu___261_1526.reify_);
            compress_uvars = (uu___261_1526.compress_uvars);
            no_full_norm = (uu___261_1526.no_full_norm);
            check_no_uvars = (uu___261_1526.check_no_uvars);
            unmeta = (uu___261_1526.unmeta);
            unascribe = (uu___261_1526.unascribe);
            in_full_norm_request = (uu___261_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___261_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___262_1527 = fs  in
          {
            beta = (uu___262_1527.beta);
            iota = false;
            zeta = (uu___262_1527.zeta);
            weak = (uu___262_1527.weak);
            hnf = (uu___262_1527.hnf);
            primops = (uu___262_1527.primops);
            do_not_unfold_pure_lets = (uu___262_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___262_1527.unfold_until);
            unfold_only = (uu___262_1527.unfold_only);
            unfold_fully = (uu___262_1527.unfold_fully);
            unfold_attr = (uu___262_1527.unfold_attr);
            unfold_tac = (uu___262_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___262_1527.pure_subterms_within_computations);
            simplify = (uu___262_1527.simplify);
            erase_universes = (uu___262_1527.erase_universes);
            allow_unbound_universes = (uu___262_1527.allow_unbound_universes);
            reify_ = (uu___262_1527.reify_);
            compress_uvars = (uu___262_1527.compress_uvars);
            no_full_norm = (uu___262_1527.no_full_norm);
            check_no_uvars = (uu___262_1527.check_no_uvars);
            unmeta = (uu___262_1527.unmeta);
            unascribe = (uu___262_1527.unascribe);
            in_full_norm_request = (uu___262_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___262_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___263_1528 = fs  in
          {
            beta = (uu___263_1528.beta);
            iota = (uu___263_1528.iota);
            zeta = false;
            weak = (uu___263_1528.weak);
            hnf = (uu___263_1528.hnf);
            primops = (uu___263_1528.primops);
            do_not_unfold_pure_lets = (uu___263_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___263_1528.unfold_until);
            unfold_only = (uu___263_1528.unfold_only);
            unfold_fully = (uu___263_1528.unfold_fully);
            unfold_attr = (uu___263_1528.unfold_attr);
            unfold_tac = (uu___263_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___263_1528.pure_subterms_within_computations);
            simplify = (uu___263_1528.simplify);
            erase_universes = (uu___263_1528.erase_universes);
            allow_unbound_universes = (uu___263_1528.allow_unbound_universes);
            reify_ = (uu___263_1528.reify_);
            compress_uvars = (uu___263_1528.compress_uvars);
            no_full_norm = (uu___263_1528.no_full_norm);
            check_no_uvars = (uu___263_1528.check_no_uvars);
            unmeta = (uu___263_1528.unmeta);
            unascribe = (uu___263_1528.unascribe);
            in_full_norm_request = (uu___263_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___263_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___264_1530 = fs  in
          {
            beta = (uu___264_1530.beta);
            iota = (uu___264_1530.iota);
            zeta = (uu___264_1530.zeta);
            weak = true;
            hnf = (uu___264_1530.hnf);
            primops = (uu___264_1530.primops);
            do_not_unfold_pure_lets = (uu___264_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___264_1530.unfold_until);
            unfold_only = (uu___264_1530.unfold_only);
            unfold_fully = (uu___264_1530.unfold_fully);
            unfold_attr = (uu___264_1530.unfold_attr);
            unfold_tac = (uu___264_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___264_1530.pure_subterms_within_computations);
            simplify = (uu___264_1530.simplify);
            erase_universes = (uu___264_1530.erase_universes);
            allow_unbound_universes = (uu___264_1530.allow_unbound_universes);
            reify_ = (uu___264_1530.reify_);
            compress_uvars = (uu___264_1530.compress_uvars);
            no_full_norm = (uu___264_1530.no_full_norm);
            check_no_uvars = (uu___264_1530.check_no_uvars);
            unmeta = (uu___264_1530.unmeta);
            unascribe = (uu___264_1530.unascribe);
            in_full_norm_request = (uu___264_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___264_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___265_1531 = fs  in
          {
            beta = (uu___265_1531.beta);
            iota = (uu___265_1531.iota);
            zeta = (uu___265_1531.zeta);
            weak = (uu___265_1531.weak);
            hnf = true;
            primops = (uu___265_1531.primops);
            do_not_unfold_pure_lets = (uu___265_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___265_1531.unfold_until);
            unfold_only = (uu___265_1531.unfold_only);
            unfold_fully = (uu___265_1531.unfold_fully);
            unfold_attr = (uu___265_1531.unfold_attr);
            unfold_tac = (uu___265_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_1531.pure_subterms_within_computations);
            simplify = (uu___265_1531.simplify);
            erase_universes = (uu___265_1531.erase_universes);
            allow_unbound_universes = (uu___265_1531.allow_unbound_universes);
            reify_ = (uu___265_1531.reify_);
            compress_uvars = (uu___265_1531.compress_uvars);
            no_full_norm = (uu___265_1531.no_full_norm);
            check_no_uvars = (uu___265_1531.check_no_uvars);
            unmeta = (uu___265_1531.unmeta);
            unascribe = (uu___265_1531.unascribe);
            in_full_norm_request = (uu___265_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___266_1532 = fs  in
          {
            beta = (uu___266_1532.beta);
            iota = (uu___266_1532.iota);
            zeta = (uu___266_1532.zeta);
            weak = (uu___266_1532.weak);
            hnf = (uu___266_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___266_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___266_1532.unfold_until);
            unfold_only = (uu___266_1532.unfold_only);
            unfold_fully = (uu___266_1532.unfold_fully);
            unfold_attr = (uu___266_1532.unfold_attr);
            unfold_tac = (uu___266_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___266_1532.pure_subterms_within_computations);
            simplify = (uu___266_1532.simplify);
            erase_universes = (uu___266_1532.erase_universes);
            allow_unbound_universes = (uu___266_1532.allow_unbound_universes);
            reify_ = (uu___266_1532.reify_);
            compress_uvars = (uu___266_1532.compress_uvars);
            no_full_norm = (uu___266_1532.no_full_norm);
            check_no_uvars = (uu___266_1532.check_no_uvars);
            unmeta = (uu___266_1532.unmeta);
            unascribe = (uu___266_1532.unascribe);
            in_full_norm_request = (uu___266_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___266_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___267_1533 = fs  in
          {
            beta = (uu___267_1533.beta);
            iota = (uu___267_1533.iota);
            zeta = (uu___267_1533.zeta);
            weak = (uu___267_1533.weak);
            hnf = (uu___267_1533.hnf);
            primops = (uu___267_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___267_1533.unfold_until);
            unfold_only = (uu___267_1533.unfold_only);
            unfold_fully = (uu___267_1533.unfold_fully);
            unfold_attr = (uu___267_1533.unfold_attr);
            unfold_tac = (uu___267_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___267_1533.pure_subterms_within_computations);
            simplify = (uu___267_1533.simplify);
            erase_universes = (uu___267_1533.erase_universes);
            allow_unbound_universes = (uu___267_1533.allow_unbound_universes);
            reify_ = (uu___267_1533.reify_);
            compress_uvars = (uu___267_1533.compress_uvars);
            no_full_norm = (uu___267_1533.no_full_norm);
            check_no_uvars = (uu___267_1533.check_no_uvars);
            unmeta = (uu___267_1533.unmeta);
            unascribe = (uu___267_1533.unascribe);
            in_full_norm_request = (uu___267_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___267_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___268_1535 = fs  in
          {
            beta = (uu___268_1535.beta);
            iota = (uu___268_1535.iota);
            zeta = (uu___268_1535.zeta);
            weak = (uu___268_1535.weak);
            hnf = (uu___268_1535.hnf);
            primops = (uu___268_1535.primops);
            do_not_unfold_pure_lets = (uu___268_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___268_1535.unfold_only);
            unfold_fully = (uu___268_1535.unfold_fully);
            unfold_attr = (uu___268_1535.unfold_attr);
            unfold_tac = (uu___268_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___268_1535.pure_subterms_within_computations);
            simplify = (uu___268_1535.simplify);
            erase_universes = (uu___268_1535.erase_universes);
            allow_unbound_universes = (uu___268_1535.allow_unbound_universes);
            reify_ = (uu___268_1535.reify_);
            compress_uvars = (uu___268_1535.compress_uvars);
            no_full_norm = (uu___268_1535.no_full_norm);
            check_no_uvars = (uu___268_1535.check_no_uvars);
            unmeta = (uu___268_1535.unmeta);
            unascribe = (uu___268_1535.unascribe);
            in_full_norm_request = (uu___268_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___268_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___269_1539 = fs  in
          {
            beta = (uu___269_1539.beta);
            iota = (uu___269_1539.iota);
            zeta = (uu___269_1539.zeta);
            weak = (uu___269_1539.weak);
            hnf = (uu___269_1539.hnf);
            primops = (uu___269_1539.primops);
            do_not_unfold_pure_lets = (uu___269_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___269_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___269_1539.unfold_fully);
            unfold_attr = (uu___269_1539.unfold_attr);
            unfold_tac = (uu___269_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___269_1539.pure_subterms_within_computations);
            simplify = (uu___269_1539.simplify);
            erase_universes = (uu___269_1539.erase_universes);
            allow_unbound_universes = (uu___269_1539.allow_unbound_universes);
            reify_ = (uu___269_1539.reify_);
            compress_uvars = (uu___269_1539.compress_uvars);
            no_full_norm = (uu___269_1539.no_full_norm);
            check_no_uvars = (uu___269_1539.check_no_uvars);
            unmeta = (uu___269_1539.unmeta);
            unascribe = (uu___269_1539.unascribe);
            in_full_norm_request = (uu___269_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___269_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___270_1545 = fs  in
          {
            beta = (uu___270_1545.beta);
            iota = (uu___270_1545.iota);
            zeta = (uu___270_1545.zeta);
            weak = (uu___270_1545.weak);
            hnf = (uu___270_1545.hnf);
            primops = (uu___270_1545.primops);
            do_not_unfold_pure_lets = (uu___270_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___270_1545.unfold_until);
            unfold_only = (uu___270_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___270_1545.unfold_attr);
            unfold_tac = (uu___270_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___270_1545.pure_subterms_within_computations);
            simplify = (uu___270_1545.simplify);
            erase_universes = (uu___270_1545.erase_universes);
            allow_unbound_universes = (uu___270_1545.allow_unbound_universes);
            reify_ = (uu___270_1545.reify_);
            compress_uvars = (uu___270_1545.compress_uvars);
            no_full_norm = (uu___270_1545.no_full_norm);
            check_no_uvars = (uu___270_1545.check_no_uvars);
            unmeta = (uu___270_1545.unmeta);
            unascribe = (uu___270_1545.unascribe);
            in_full_norm_request = (uu___270_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___270_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___271_1549 = fs  in
          {
            beta = (uu___271_1549.beta);
            iota = (uu___271_1549.iota);
            zeta = (uu___271_1549.zeta);
            weak = (uu___271_1549.weak);
            hnf = (uu___271_1549.hnf);
            primops = (uu___271_1549.primops);
            do_not_unfold_pure_lets = (uu___271_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___271_1549.unfold_until);
            unfold_only = (uu___271_1549.unfold_only);
            unfold_fully = (uu___271_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___271_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___271_1549.pure_subterms_within_computations);
            simplify = (uu___271_1549.simplify);
            erase_universes = (uu___271_1549.erase_universes);
            allow_unbound_universes = (uu___271_1549.allow_unbound_universes);
            reify_ = (uu___271_1549.reify_);
            compress_uvars = (uu___271_1549.compress_uvars);
            no_full_norm = (uu___271_1549.no_full_norm);
            check_no_uvars = (uu___271_1549.check_no_uvars);
            unmeta = (uu___271_1549.unmeta);
            unascribe = (uu___271_1549.unascribe);
            in_full_norm_request = (uu___271_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___271_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___272_1550 = fs  in
          {
            beta = (uu___272_1550.beta);
            iota = (uu___272_1550.iota);
            zeta = (uu___272_1550.zeta);
            weak = (uu___272_1550.weak);
            hnf = (uu___272_1550.hnf);
            primops = (uu___272_1550.primops);
            do_not_unfold_pure_lets = (uu___272_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___272_1550.unfold_until);
            unfold_only = (uu___272_1550.unfold_only);
            unfold_fully = (uu___272_1550.unfold_fully);
            unfold_attr = (uu___272_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___272_1550.pure_subterms_within_computations);
            simplify = (uu___272_1550.simplify);
            erase_universes = (uu___272_1550.erase_universes);
            allow_unbound_universes = (uu___272_1550.allow_unbound_universes);
            reify_ = (uu___272_1550.reify_);
            compress_uvars = (uu___272_1550.compress_uvars);
            no_full_norm = (uu___272_1550.no_full_norm);
            check_no_uvars = (uu___272_1550.check_no_uvars);
            unmeta = (uu___272_1550.unmeta);
            unascribe = (uu___272_1550.unascribe);
            in_full_norm_request = (uu___272_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___272_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___273_1551 = fs  in
          {
            beta = (uu___273_1551.beta);
            iota = (uu___273_1551.iota);
            zeta = (uu___273_1551.zeta);
            weak = (uu___273_1551.weak);
            hnf = (uu___273_1551.hnf);
            primops = (uu___273_1551.primops);
            do_not_unfold_pure_lets = (uu___273_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___273_1551.unfold_until);
            unfold_only = (uu___273_1551.unfold_only);
            unfold_fully = (uu___273_1551.unfold_fully);
            unfold_attr = (uu___273_1551.unfold_attr);
            unfold_tac = (uu___273_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___273_1551.simplify);
            erase_universes = (uu___273_1551.erase_universes);
            allow_unbound_universes = (uu___273_1551.allow_unbound_universes);
            reify_ = (uu___273_1551.reify_);
            compress_uvars = (uu___273_1551.compress_uvars);
            no_full_norm = (uu___273_1551.no_full_norm);
            check_no_uvars = (uu___273_1551.check_no_uvars);
            unmeta = (uu___273_1551.unmeta);
            unascribe = (uu___273_1551.unascribe);
            in_full_norm_request = (uu___273_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___273_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___274_1552 = fs  in
          {
            beta = (uu___274_1552.beta);
            iota = (uu___274_1552.iota);
            zeta = (uu___274_1552.zeta);
            weak = (uu___274_1552.weak);
            hnf = (uu___274_1552.hnf);
            primops = (uu___274_1552.primops);
            do_not_unfold_pure_lets = (uu___274_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___274_1552.unfold_until);
            unfold_only = (uu___274_1552.unfold_only);
            unfold_fully = (uu___274_1552.unfold_fully);
            unfold_attr = (uu___274_1552.unfold_attr);
            unfold_tac = (uu___274_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___274_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___274_1552.erase_universes);
            allow_unbound_universes = (uu___274_1552.allow_unbound_universes);
            reify_ = (uu___274_1552.reify_);
            compress_uvars = (uu___274_1552.compress_uvars);
            no_full_norm = (uu___274_1552.no_full_norm);
            check_no_uvars = (uu___274_1552.check_no_uvars);
            unmeta = (uu___274_1552.unmeta);
            unascribe = (uu___274_1552.unascribe);
            in_full_norm_request = (uu___274_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___274_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___275_1553 = fs  in
          {
            beta = (uu___275_1553.beta);
            iota = (uu___275_1553.iota);
            zeta = (uu___275_1553.zeta);
            weak = (uu___275_1553.weak);
            hnf = (uu___275_1553.hnf);
            primops = (uu___275_1553.primops);
            do_not_unfold_pure_lets = (uu___275_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___275_1553.unfold_until);
            unfold_only = (uu___275_1553.unfold_only);
            unfold_fully = (uu___275_1553.unfold_fully);
            unfold_attr = (uu___275_1553.unfold_attr);
            unfold_tac = (uu___275_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___275_1553.pure_subterms_within_computations);
            simplify = (uu___275_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___275_1553.allow_unbound_universes);
            reify_ = (uu___275_1553.reify_);
            compress_uvars = (uu___275_1553.compress_uvars);
            no_full_norm = (uu___275_1553.no_full_norm);
            check_no_uvars = (uu___275_1553.check_no_uvars);
            unmeta = (uu___275_1553.unmeta);
            unascribe = (uu___275_1553.unascribe);
            in_full_norm_request = (uu___275_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___275_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___276_1554 = fs  in
          {
            beta = (uu___276_1554.beta);
            iota = (uu___276_1554.iota);
            zeta = (uu___276_1554.zeta);
            weak = (uu___276_1554.weak);
            hnf = (uu___276_1554.hnf);
            primops = (uu___276_1554.primops);
            do_not_unfold_pure_lets = (uu___276_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___276_1554.unfold_until);
            unfold_only = (uu___276_1554.unfold_only);
            unfold_fully = (uu___276_1554.unfold_fully);
            unfold_attr = (uu___276_1554.unfold_attr);
            unfold_tac = (uu___276_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___276_1554.pure_subterms_within_computations);
            simplify = (uu___276_1554.simplify);
            erase_universes = (uu___276_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___276_1554.reify_);
            compress_uvars = (uu___276_1554.compress_uvars);
            no_full_norm = (uu___276_1554.no_full_norm);
            check_no_uvars = (uu___276_1554.check_no_uvars);
            unmeta = (uu___276_1554.unmeta);
            unascribe = (uu___276_1554.unascribe);
            in_full_norm_request = (uu___276_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___276_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___277_1555 = fs  in
          {
            beta = (uu___277_1555.beta);
            iota = (uu___277_1555.iota);
            zeta = (uu___277_1555.zeta);
            weak = (uu___277_1555.weak);
            hnf = (uu___277_1555.hnf);
            primops = (uu___277_1555.primops);
            do_not_unfold_pure_lets = (uu___277_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___277_1555.unfold_until);
            unfold_only = (uu___277_1555.unfold_only);
            unfold_fully = (uu___277_1555.unfold_fully);
            unfold_attr = (uu___277_1555.unfold_attr);
            unfold_tac = (uu___277_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___277_1555.pure_subterms_within_computations);
            simplify = (uu___277_1555.simplify);
            erase_universes = (uu___277_1555.erase_universes);
            allow_unbound_universes = (uu___277_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___277_1555.compress_uvars);
            no_full_norm = (uu___277_1555.no_full_norm);
            check_no_uvars = (uu___277_1555.check_no_uvars);
            unmeta = (uu___277_1555.unmeta);
            unascribe = (uu___277_1555.unascribe);
            in_full_norm_request = (uu___277_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___277_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___278_1556 = fs  in
          {
            beta = (uu___278_1556.beta);
            iota = (uu___278_1556.iota);
            zeta = (uu___278_1556.zeta);
            weak = (uu___278_1556.weak);
            hnf = (uu___278_1556.hnf);
            primops = (uu___278_1556.primops);
            do_not_unfold_pure_lets = (uu___278_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___278_1556.unfold_until);
            unfold_only = (uu___278_1556.unfold_only);
            unfold_fully = (uu___278_1556.unfold_fully);
            unfold_attr = (uu___278_1556.unfold_attr);
            unfold_tac = (uu___278_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___278_1556.pure_subterms_within_computations);
            simplify = (uu___278_1556.simplify);
            erase_universes = (uu___278_1556.erase_universes);
            allow_unbound_universes = (uu___278_1556.allow_unbound_universes);
            reify_ = (uu___278_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___278_1556.no_full_norm);
            check_no_uvars = (uu___278_1556.check_no_uvars);
            unmeta = (uu___278_1556.unmeta);
            unascribe = (uu___278_1556.unascribe);
            in_full_norm_request = (uu___278_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___278_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___279_1557 = fs  in
          {
            beta = (uu___279_1557.beta);
            iota = (uu___279_1557.iota);
            zeta = (uu___279_1557.zeta);
            weak = (uu___279_1557.weak);
            hnf = (uu___279_1557.hnf);
            primops = (uu___279_1557.primops);
            do_not_unfold_pure_lets = (uu___279_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___279_1557.unfold_until);
            unfold_only = (uu___279_1557.unfold_only);
            unfold_fully = (uu___279_1557.unfold_fully);
            unfold_attr = (uu___279_1557.unfold_attr);
            unfold_tac = (uu___279_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___279_1557.pure_subterms_within_computations);
            simplify = (uu___279_1557.simplify);
            erase_universes = (uu___279_1557.erase_universes);
            allow_unbound_universes = (uu___279_1557.allow_unbound_universes);
            reify_ = (uu___279_1557.reify_);
            compress_uvars = (uu___279_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___279_1557.check_no_uvars);
            unmeta = (uu___279_1557.unmeta);
            unascribe = (uu___279_1557.unascribe);
            in_full_norm_request = (uu___279_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___279_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___280_1558 = fs  in
          {
            beta = (uu___280_1558.beta);
            iota = (uu___280_1558.iota);
            zeta = (uu___280_1558.zeta);
            weak = (uu___280_1558.weak);
            hnf = (uu___280_1558.hnf);
            primops = (uu___280_1558.primops);
            do_not_unfold_pure_lets = (uu___280_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___280_1558.unfold_until);
            unfold_only = (uu___280_1558.unfold_only);
            unfold_fully = (uu___280_1558.unfold_fully);
            unfold_attr = (uu___280_1558.unfold_attr);
            unfold_tac = (uu___280_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___280_1558.pure_subterms_within_computations);
            simplify = (uu___280_1558.simplify);
            erase_universes = (uu___280_1558.erase_universes);
            allow_unbound_universes = (uu___280_1558.allow_unbound_universes);
            reify_ = (uu___280_1558.reify_);
            compress_uvars = (uu___280_1558.compress_uvars);
            no_full_norm = (uu___280_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___280_1558.unmeta);
            unascribe = (uu___280_1558.unascribe);
            in_full_norm_request = (uu___280_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___280_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___281_1559 = fs  in
          {
            beta = (uu___281_1559.beta);
            iota = (uu___281_1559.iota);
            zeta = (uu___281_1559.zeta);
            weak = (uu___281_1559.weak);
            hnf = (uu___281_1559.hnf);
            primops = (uu___281_1559.primops);
            do_not_unfold_pure_lets = (uu___281_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___281_1559.unfold_until);
            unfold_only = (uu___281_1559.unfold_only);
            unfold_fully = (uu___281_1559.unfold_fully);
            unfold_attr = (uu___281_1559.unfold_attr);
            unfold_tac = (uu___281_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___281_1559.pure_subterms_within_computations);
            simplify = (uu___281_1559.simplify);
            erase_universes = (uu___281_1559.erase_universes);
            allow_unbound_universes = (uu___281_1559.allow_unbound_universes);
            reify_ = (uu___281_1559.reify_);
            compress_uvars = (uu___281_1559.compress_uvars);
            no_full_norm = (uu___281_1559.no_full_norm);
            check_no_uvars = (uu___281_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___281_1559.unascribe);
            in_full_norm_request = (uu___281_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___281_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___282_1560 = fs  in
          {
            beta = (uu___282_1560.beta);
            iota = (uu___282_1560.iota);
            zeta = (uu___282_1560.zeta);
            weak = (uu___282_1560.weak);
            hnf = (uu___282_1560.hnf);
            primops = (uu___282_1560.primops);
            do_not_unfold_pure_lets = (uu___282_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___282_1560.unfold_until);
            unfold_only = (uu___282_1560.unfold_only);
            unfold_fully = (uu___282_1560.unfold_fully);
            unfold_attr = (uu___282_1560.unfold_attr);
            unfold_tac = (uu___282_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___282_1560.pure_subterms_within_computations);
            simplify = (uu___282_1560.simplify);
            erase_universes = (uu___282_1560.erase_universes);
            allow_unbound_universes = (uu___282_1560.allow_unbound_universes);
            reify_ = (uu___282_1560.reify_);
            compress_uvars = (uu___282_1560.compress_uvars);
            no_full_norm = (uu___282_1560.no_full_norm);
            check_no_uvars = (uu___282_1560.check_no_uvars);
            unmeta = (uu___282_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___282_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___282_1560.weakly_reduce_scrutinee)
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
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
    }
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
  | Dummy 
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
    FStar_Pervasives_Native.tuple2 Prims.list
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  unfolding: Prims.bool ;
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
        wpe = __fname__wpe; norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop;
        unfolding = __fname__unfolding; b380 = __fname__b380;
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
  normalize_pure_lets: Prims.bool }
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
             let uu____2374 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2374 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2388 = FStar_Util.psmap_empty ()  in add_steps uu____2388 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2403 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2403
  
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list
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
  FStar_Pervasives_Native.tuple2 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2561 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2599 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2637 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2710 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2760 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2818 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2862 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2902 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2940 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2958 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2985 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2985 with | (hd1,uu____2999) -> hd1
  
let mk :
  'Auu____3022 .
    'Auu____3022 ->
      FStar_Range.range -> 'Auu____3022 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3085 = FStar_ST.op_Bang r  in
          match uu____3085 with
          | FStar_Pervasives_Native.Some uu____3137 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3213 =
      FStar_List.map
        (fun uu____3227  ->
           match uu____3227 with
           | (bopt,c) ->
               let uu____3240 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3242 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3240 uu____3242) env
       in
    FStar_All.pipe_right uu____3213 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___240_3245  ->
    match uu___240_3245 with
    | Clos (env,t,uu____3248,uu____3249) ->
        let uu____3294 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3301 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3294 uu____3301
    | Univ uu____3302 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___241_3307  ->
    match uu___241_3307 with
    | Arg (c,uu____3309,uu____3310) ->
        let uu____3311 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3311
    | MemoLazy uu____3312 -> "MemoLazy"
    | Abs (uu____3319,bs,uu____3321,uu____3322,uu____3323) ->
        let uu____3328 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3328
    | UnivArgs uu____3333 -> "UnivArgs"
    | Match uu____3340 -> "Match"
    | App (uu____3349,t,uu____3351,uu____3352) ->
        let uu____3353 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3353
    | Meta (uu____3354,m,uu____3356) -> "Meta"
    | Let uu____3357 -> "Let"
    | Cfg uu____3366 -> "Cfg"
    | Debug (t,uu____3368) ->
        let uu____3369 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3369
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3379 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3379 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let is_empty : 'Auu____3436 . 'Auu____3436 Prims.list -> Prims.bool =
  fun uu___242_3443  ->
    match uu___242_3443 with | [] -> true | uu____3446 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3478 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3478
      with
      | uu____3497 ->
          let uu____3498 =
            let uu____3499 = FStar_Syntax_Print.db_to_string x  in
            let uu____3500 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3499
              uu____3500
             in
          failwith uu____3498
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3508 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3508
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3512 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3512
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3516 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3516
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
          let uu____3550 =
            FStar_List.fold_left
              (fun uu____3576  ->
                 fun u1  ->
                   match uu____3576 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3601 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3601 with
                        | (k_u,n1) ->
                            let uu____3616 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3616
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3550 with
          | (uu____3634,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3661 =
                   let uu____3662 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3662  in
                 match uu____3661 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3680 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3688 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3694 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3703 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3712 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3719 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3719 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3736 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3736 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3744 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3752 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3752 with
                                  | (uu____3757,m) -> n1 <= m))
                           in
                        if uu____3744 then rest1 else us1
                    | uu____3762 -> us1)
               | uu____3767 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3771 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3771
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3775 = aux u  in
           match uu____3775 with
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
            (fun uu____3923  ->
               let uu____3924 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3925 = env_to_string env  in
               let uu____3926 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3924 uu____3925 uu____3926);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3935 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3938 ->
                    let uu____3963 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3963
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3964 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3965 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3966 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3967 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3995 ->
                           let uu____4010 =
                             let uu____4011 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4012 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4011 uu____4012
                              in
                           failwith uu____4010
                       | uu____4015 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___243_4052  ->
                                         match uu___243_4052 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4059 =
                                               let uu____4066 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4066)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4059
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___287_4076 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___287_4076.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___287_4076.FStar_Syntax_Syntax.sort)
                                                  })
                                                in
                                             let t1 =
                                               inline_closure_env cfg env []
                                                 x_i
                                                in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____4081 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4084 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___288_4088 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___288_4088.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___288_4088.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4115 =
                        let uu____4116 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4116  in
                      mk uu____4115 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4124 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4124  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4126 = lookup_bvar env x  in
                    (match uu____4126 with
                     | Univ uu____4129 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___289_4133 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___289_4133.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___289_4133.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4139,uu____4140) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4225  ->
                              fun stack1  ->
                                match uu____4225 with
                                | (a,aq) ->
                                    let uu____4237 =
                                      let uu____4238 =
                                        let uu____4245 =
                                          let uu____4246 =
                                            let uu____4277 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4277, false)  in
                                          Clos uu____4246  in
                                        (uu____4245, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4238  in
                                    uu____4237 :: stack1) args)
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
                    let uu____4453 = close_binders cfg env bs  in
                    (match uu____4453 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4500 =
                      let uu____4511 =
                        let uu____4518 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4518]  in
                      close_binders cfg env uu____4511  in
                    (match uu____4500 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4553 =
                             let uu____4554 =
                               let uu____4561 =
                                 let uu____4562 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4562
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4561, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4554  in
                           mk uu____4553 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4653 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4653
                      | FStar_Util.Inr c ->
                          let uu____4667 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4667
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4686 =
                        let uu____4687 =
                          let uu____4714 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4714, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4687  in
                      mk uu____4686 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4760 =
                            let uu____4761 =
                              let uu____4768 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4768, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4761  in
                          mk uu____4760 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4820  -> dummy :: env1) env
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
                    let uu____4841 =
                      let uu____4852 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4852
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4871 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___290_4887 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___290_4887.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___290_4887.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4871))
                       in
                    (match uu____4841 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___291_4905 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___291_4905.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___291_4905.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___291_4905.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___291_4905.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4919,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4982  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4999 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4999
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5011  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5035 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5035
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___292_5043 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___292_5043.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___292_5043.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___293_5044 = lb  in
                      let uu____5045 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___293_5044.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___293_5044.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5045;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___293_5044.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___293_5044.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5077  -> fun env1  -> dummy :: env1)
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
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____5166  ->
               let uu____5167 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5168 = env_to_string env  in
               let uu____5169 = stack_to_string stack  in
               let uu____5170 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5167 uu____5168 uu____5169 uu____5170);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5175,uu____5176),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5253 = close_binders cfg env' bs  in
               (match uu____5253 with
                | (bs1,uu____5267) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5283 =
                      let uu___294_5286 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___294_5286.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___294_5286.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5283)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5342 =
                 match uu____5342 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5457 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5486 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5570  ->
                                     fun uu____5571  ->
                                       match (uu____5570, uu____5571) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5710 = norm_pat env4 p1
                                              in
                                           (match uu____5710 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5486 with
                            | (pats1,env4) ->
                                ((let uu___295_5872 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___295_5872.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___296_5891 = x  in
                             let uu____5892 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___296_5891.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___296_5891.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5892
                             }  in
                           ((let uu___297_5906 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___297_5906.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___298_5917 = x  in
                             let uu____5918 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___298_5917.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___298_5917.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5918
                             }  in
                           ((let uu___299_5932 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___299_5932.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___300_5948 = x  in
                             let uu____5949 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___300_5948.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___300_5948.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5949
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___301_5966 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___301_5966.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5971 = norm_pat env2 pat  in
                     (match uu____5971 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6040 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6040
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6059 =
                   let uu____6060 =
                     let uu____6083 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6083)  in
                   FStar_Syntax_Syntax.Tm_match uu____6060  in
                 mk uu____6059 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6196 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6285  ->
                                       match uu____6285 with
                                       | (a,q) ->
                                           let uu____6304 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6304, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6196
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6315 =
                       let uu____6322 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6322)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6315
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6334 =
                       let uu____6343 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6343)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6334
                 | uu____6348 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6354 -> failwith "Impossible: unexpected stack element")

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
        let uu____6368 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6441  ->
                  fun uu____6442  ->
                    match (uu____6441, uu____6442) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___302_6560 = b  in
                          let uu____6561 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___302_6560.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___302_6560.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6561
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6368 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6678 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6691 = inline_closure_env cfg env [] t  in
                 let uu____6692 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6691 uu____6692
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6705 = inline_closure_env cfg env [] t  in
                 let uu____6706 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6705 uu____6706
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6750  ->
                           match uu____6750 with
                           | (a,q) ->
                               let uu____6763 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6763, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___244_6778  ->
                           match uu___244_6778 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6782 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6782
                           | f -> f))
                    in
                 let uu____6786 =
                   let uu___303_6787 = c1  in
                   let uu____6788 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6788;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___303_6787.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6786)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___245_6798  ->
            match uu___245_6798 with
            | FStar_Syntax_Syntax.DECREASES uu____6799 -> false
            | uu____6802 -> true))

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
                   (fun uu___246_6820  ->
                      match uu___246_6820 with
                      | FStar_Syntax_Syntax.DECREASES uu____6821 -> false
                      | uu____6824 -> true))
               in
            let rc1 =
              let uu___304_6826 = rc  in
              let uu____6827 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___304_6826.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6827;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6836 -> lopt

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
    let uu____6941 =
      let uu____6950 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6950  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6941  in
  let arg_as_bounded_int uu____6976 =
    match uu____6976 with
    | (a,uu____6988) ->
        let uu____6995 =
          let uu____6996 = FStar_Syntax_Subst.compress a  in
          uu____6996.FStar_Syntax_Syntax.n  in
        (match uu____6995 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____7006;
                FStar_Syntax_Syntax.vars = uu____7007;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____7009;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____7010;_},uu____7011)::[])
             when
             let uu____7050 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7050 "int_to_t" ->
             let uu____7051 =
               let uu____7056 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7056)  in
             FStar_Pervasives_Native.Some uu____7051
         | uu____7061 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7109 = f a  in FStar_Pervasives_Native.Some uu____7109
    | uu____7110 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7166 = f a0 a1  in FStar_Pervasives_Native.Some uu____7166
    | uu____7167 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7225 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7225  in
  let binary_op as_a f res args =
    let uu____7296 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7296  in
  let as_primitive_step is_strong uu____7333 =
    match uu____7333 with
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
           let uu____7393 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7393)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7429 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7429)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7458 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7458)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7494 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7494)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7530 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7530)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7662 =
          let uu____7671 = as_a a  in
          let uu____7674 = as_b b  in (uu____7671, uu____7674)  in
        (match uu____7662 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7689 =
               let uu____7690 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7690  in
             FStar_Pervasives_Native.Some uu____7689
         | uu____7691 -> FStar_Pervasives_Native.None)
    | uu____7700 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7720 =
        let uu____7721 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7721  in
      mk uu____7720 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7735 =
      let uu____7738 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7738  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7735  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7780 =
      let uu____7781 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7781  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7780
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7845 = arg_as_string a1  in
        (match uu____7845 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7851 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7851 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7864 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7864
              | uu____7865 -> FStar_Pervasives_Native.None)
         | uu____7870 -> FStar_Pervasives_Native.None)
    | uu____7873 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7893 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7893
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7930 =
          let uu____7951 = arg_as_string fn  in
          let uu____7954 = arg_as_int from_line  in
          let uu____7957 = arg_as_int from_col  in
          let uu____7960 = arg_as_int to_line  in
          let uu____7963 = arg_as_int to_col  in
          (uu____7951, uu____7954, uu____7957, uu____7960, uu____7963)  in
        (match uu____7930 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7994 =
                 let uu____7995 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7996 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7995 uu____7996  in
               let uu____7997 =
                 let uu____7998 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7999 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7998 uu____7999  in
               FStar_Range.mk_range fn1 uu____7994 uu____7997  in
             let uu____8000 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8000
         | uu____8001 -> FStar_Pervasives_Native.None)
    | uu____8022 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8055)::(a1,uu____8057)::(a2,uu____8059)::[] ->
        let uu____8096 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8096 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8101 -> FStar_Pervasives_Native.None)
    | uu____8102 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8133)::[] ->
        let uu____8142 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8142 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8148 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8148
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8149 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8175 =
      let uu____8192 =
        let uu____8209 =
          let uu____8226 =
            let uu____8243 =
              let uu____8260 =
                let uu____8277 =
                  let uu____8294 =
                    let uu____8311 =
                      let uu____8328 =
                        let uu____8345 =
                          let uu____8362 =
                            let uu____8379 =
                              let uu____8396 =
                                let uu____8413 =
                                  let uu____8430 =
                                    let uu____8447 =
                                      let uu____8464 =
                                        let uu____8481 =
                                          let uu____8498 =
                                            let uu____8515 =
                                              let uu____8532 =
                                                let uu____8547 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8547,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8556 =
                                                let uu____8573 =
                                                  let uu____8588 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8588,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8601 =
                                                  let uu____8618 =
                                                    let uu____8633 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8633,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8642 =
                                                    let uu____8659 =
                                                      let uu____8674 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8674,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8659]  in
                                                  uu____8618 :: uu____8642
                                                   in
                                                uu____8573 :: uu____8601  in
                                              uu____8532 :: uu____8556  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8515
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8498
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8481
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8464
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8447
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8894 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8894 y)))
                                    :: uu____8430
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8413
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8396
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8379
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8362
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8345
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8328
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9089 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9089)))
                      :: uu____8311
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9119 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9119)))
                    :: uu____8294
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9149 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9149)))
                  :: uu____8277
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9179 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9179)))
                :: uu____8260
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8243
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8226
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8209
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8192
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8175
     in
  let weak_ops =
    let uu____9334 =
      let uu____9349 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9349, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9334]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9429 =
        let uu____9434 =
          let uu____9435 = FStar_Syntax_Syntax.as_arg c  in [uu____9435]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9434  in
      uu____9429 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9509 =
                let uu____9524 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9524, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9546  ->
                          fun uu____9547  ->
                            match (uu____9546, uu____9547) with
                            | ((int_to_t1,x),(uu____9566,y)) ->
                                let uu____9576 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9576)))
                 in
              let uu____9577 =
                let uu____9594 =
                  let uu____9609 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9609, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9631  ->
                            fun uu____9632  ->
                              match (uu____9631, uu____9632) with
                              | ((int_to_t1,x),(uu____9651,y)) ->
                                  let uu____9661 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9661)))
                   in
                let uu____9662 =
                  let uu____9679 =
                    let uu____9694 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9694, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9716  ->
                              fun uu____9717  ->
                                match (uu____9716, uu____9717) with
                                | ((int_to_t1,x),(uu____9736,y)) ->
                                    let uu____9746 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9746)))
                     in
                  let uu____9747 =
                    let uu____9764 =
                      let uu____9779 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9779, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9797  ->
                                match uu____9797 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9764]  in
                  uu____9679 :: uu____9747  in
                uu____9594 :: uu____9662  in
              uu____9509 :: uu____9577))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9927 =
                let uu____9942 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9942, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9964  ->
                          fun uu____9965  ->
                            match (uu____9964, uu____9965) with
                            | ((int_to_t1,x),(uu____9984,y)) ->
                                let uu____9994 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9994)))
                 in
              let uu____9995 =
                let uu____10012 =
                  let uu____10027 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10027, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10049  ->
                            fun uu____10050  ->
                              match (uu____10049, uu____10050) with
                              | ((int_to_t1,x),(uu____10069,y)) ->
                                  let uu____10079 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10079)))
                   in
                [uu____10012]  in
              uu____9927 :: uu____9995))
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
    | (_typ,uu____10209)::(a1,uu____10211)::(a2,uu____10213)::[] ->
        let uu____10250 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10250 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___305_10254 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___305_10254.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___305_10254.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10256 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10256.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10256.FStar_Syntax_Syntax.vars)
                })
         | uu____10257 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10259)::uu____10260::(a1,uu____10262)::(a2,uu____10264)::[]
        ->
        let uu____10313 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10313 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___305_10317 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___305_10317.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___305_10317.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10319 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10319.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10319.FStar_Syntax_Syntax.vars)
                })
         | uu____10320 -> FStar_Pervasives_Native.None)
    | uu____10321 -> failwith "Unexpected number of arguments"  in
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
    let uu____10375 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10375 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10427 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10427) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10489  ->
           fun subst1  ->
             match uu____10489 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10530,uu____10531)) ->
                      let uu____10590 = b  in
                      (match uu____10590 with
                       | (bv,uu____10598) ->
                           let uu____10599 =
                             let uu____10600 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10600  in
                           if uu____10599
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10605 = unembed_binder term1  in
                              match uu____10605 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10612 =
                                      let uu___307_10613 = bv  in
                                      let uu____10614 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___307_10613.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___307_10613.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10614
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10612
                                     in
                                  let b_for_x =
                                    let uu____10618 =
                                      let uu____10625 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10625)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10618  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___247_10639  ->
                                         match uu___247_10639 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10640,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10642;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10643;_})
                                             ->
                                             let uu____10648 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10648
                                         | uu____10649 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10650 -> subst1)) env []
  
let reduce_primops :
  'Auu____10673 'Auu____10674 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10673) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10674 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10722 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10722 with
             | (head1,args) ->
                 let uu____10761 =
                   let uu____10762 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10762.FStar_Syntax_Syntax.n  in
                 (match uu____10761 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10768 = find_prim_step cfg fv  in
                      (match uu____10768 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10794  ->
                                   let uu____10795 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10796 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10803 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10795 uu____10796 uu____10803);
                              tm)
                           else
                             (let uu____10805 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10805 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10918  ->
                                        let uu____10919 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10919);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10922  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10924 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10924 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10932  ->
                                              let uu____10933 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10933);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10939  ->
                                              let uu____10940 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10941 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10940 uu____10941);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10942 ->
                           (log_primops cfg
                              (fun uu____10946  ->
                                 let uu____10947 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10947);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10951  ->
                            let uu____10952 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10952);
                       (match args with
                        | (a1,uu____10956)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10973 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10985  ->
                            let uu____10986 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10986);
                       (match args with
                        | (t,uu____10990)::(r,uu____10992)::[] ->
                            let uu____11019 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11019 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11025 -> tm))
                  | uu____11034 -> tm))
  
let reduce_equality :
  'Auu____11045 'Auu____11046 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11045) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11046 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___308_11092 = cfg  in
         {
           steps =
             (let uu___309_11095 = default_steps  in
              {
                beta = (uu___309_11095.beta);
                iota = (uu___309_11095.iota);
                zeta = (uu___309_11095.zeta);
                weak = (uu___309_11095.weak);
                hnf = (uu___309_11095.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___309_11095.do_not_unfold_pure_lets);
                unfold_until = (uu___309_11095.unfold_until);
                unfold_only = (uu___309_11095.unfold_only);
                unfold_fully = (uu___309_11095.unfold_fully);
                unfold_attr = (uu___309_11095.unfold_attr);
                unfold_tac = (uu___309_11095.unfold_tac);
                pure_subterms_within_computations =
                  (uu___309_11095.pure_subterms_within_computations);
                simplify = (uu___309_11095.simplify);
                erase_universes = (uu___309_11095.erase_universes);
                allow_unbound_universes =
                  (uu___309_11095.allow_unbound_universes);
                reify_ = (uu___309_11095.reify_);
                compress_uvars = (uu___309_11095.compress_uvars);
                no_full_norm = (uu___309_11095.no_full_norm);
                check_no_uvars = (uu___309_11095.check_no_uvars);
                unmeta = (uu___309_11095.unmeta);
                unascribe = (uu___309_11095.unascribe);
                in_full_norm_request = (uu___309_11095.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___309_11095.weakly_reduce_scrutinee)
              });
           tcenv = (uu___308_11092.tcenv);
           debug = (uu___308_11092.debug);
           delta_level = (uu___308_11092.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___308_11092.strong);
           memoize_lazy = (uu___308_11092.memoize_lazy);
           normalize_pure_lets = (uu___308_11092.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11102 .
    FStar_Syntax_Syntax.term -> 'Auu____11102 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11117 =
        let uu____11124 =
          let uu____11125 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11125.FStar_Syntax_Syntax.n  in
        (uu____11124, args)  in
      match uu____11117 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11131::uu____11132::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11136::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11141::uu____11142::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11145 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___248_11158  ->
    match uu___248_11158 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11164 =
          let uu____11167 =
            let uu____11168 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11168  in
          [uu____11167]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11164
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11174 =
          let uu____11177 =
            let uu____11178 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11178  in
          [uu____11177]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11174
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11201 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11201)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11252 =
            let uu____11257 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11257 s  in
          match uu____11252 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11273 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11273
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11299::(tm,uu____11301)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11330)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11351)::uu____11352::(tm,uu____11354)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11395 =
              let uu____11400 = full_norm steps  in parse_steps uu____11400
               in
            (match uu____11395 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11439 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___249_11458  ->
    match uu___249_11458 with
    | (App
        (uu____11461,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11462;
                       FStar_Syntax_Syntax.vars = uu____11463;_},uu____11464,uu____11465))::uu____11466
        -> true
    | uu____11471 -> false
  
let firstn :
  'Auu____11480 .
    Prims.int ->
      'Auu____11480 Prims.list ->
        ('Auu____11480 Prims.list,'Auu____11480 Prims.list)
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
          (uu____11522,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11523;
                         FStar_Syntax_Syntax.vars = uu____11524;_},uu____11525,uu____11526))::uu____11527
          -> (cfg.steps).reify_
      | uu____11532 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11555) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11565) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11584  ->
                  match uu____11584 with
                  | (a,uu____11592) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11598 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11623 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11624 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11639 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11640 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11641 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11642 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11643 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11644 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11651 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11658 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11671 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11688 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11701 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11708 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11770  ->
                   match uu____11770 with
                   | (a,uu____11778) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11785) ->
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
                     (fun uu____11907  ->
                        match uu____11907 with
                        | (a,uu____11915) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11920,uu____11921,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11927,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11933 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11940 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11941 -> false))
  
let decide_unfolding :
  'Auu____11956 .
    cfg ->
      'Auu____11956 ->
        stack_elt Prims.list ->
          FStar_Range.range ->
            FStar_Syntax_Syntax.fv ->
              (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
                  FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                                   FStar_Syntax_Syntax.universes
                                                     FStar_Pervasives_Native.option)
                                                   FStar_Pervasives_Native.tuple2)
                 FStar_Util.either,FStar_Range.range)
                FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
                ->
                (cfg,stack_elt Prims.list) FStar_Pervasives_Native.tuple2
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              let attrs =
                let uu____12042 =
                  FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                match uu____12042 with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some ats -> ats  in
              let yes = (true, false, false)  in
              let no = (false, false, false)  in
              let fully = (true, true, false)  in
              let reif = (true, false, true)  in
              let yesno b = if b then yes else no  in
              let fullyno b = if b then fully else no  in
              let comb_or l =
                FStar_List.fold_right
                  (fun uu____12170  ->
                     fun uu____12171  ->
                       match (uu____12170, uu____12171) with
                       | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                  l (false, false, false)
                 in
              let string_of_res uu____12231 =
                match uu____12231 with
                | (x,y,z) ->
                    let uu____12241 = FStar_Util.string_of_bool x  in
                    let uu____12242 = FStar_Util.string_of_bool y  in
                    let uu____12243 = FStar_Util.string_of_bool z  in
                    FStar_Util.format3 "(%s,%s,%s)" uu____12241 uu____12242
                      uu____12243
                 in
              let res =
                match (qninfo, ((cfg.steps).unfold_only),
                        ((cfg.steps).unfold_fully),
                        ((cfg.steps).unfold_attr))
                with
                | uu____12289 when
                    FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                    let b = should_reify cfg stack  in
                    (log_unfolding cfg
                       (fun uu____12335  ->
                          let uu____12336 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          let uu____12337 = FStar_Util.string_of_bool b  in
                          FStar_Util.print2
                            ">>> For DM4F action %s, should_reify = %s\n"
                            uu____12336 uu____12337);
                     if b then reif else no)
                | uu____12345 when
                    let uu____12386 = find_prim_step cfg fv  in
                    FStar_Option.isSome uu____12386 -> no
                | (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr
                    ({
                       FStar_Syntax_Syntax.sigel =
                         FStar_Syntax_Syntax.Sig_let
                         ((is_rec,uu____12390),uu____12391);
                       FStar_Syntax_Syntax.sigrng = uu____12392;
                       FStar_Syntax_Syntax.sigquals = qs;
                       FStar_Syntax_Syntax.sigmeta = uu____12394;
                       FStar_Syntax_Syntax.sigattrs = uu____12395;_},uu____12396),uu____12397),uu____12398,uu____12399,uu____12400)
                    when
                    FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                      qs
                    -> no
                | (uu____12503,uu____12504,uu____12505,uu____12506) when
                    (cfg.steps).unfold_tac &&
                      (FStar_Util.for_some
                         (FStar_Syntax_Util.attr_eq
                            FStar_Syntax_Util.tac_opaque_attr) attrs)
                    -> no
                | (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr
                    ({
                       FStar_Syntax_Syntax.sigel =
                         FStar_Syntax_Syntax.Sig_let
                         ((is_rec,uu____12572),uu____12573);
                       FStar_Syntax_Syntax.sigrng = uu____12574;
                       FStar_Syntax_Syntax.sigquals = qs;
                       FStar_Syntax_Syntax.sigmeta = uu____12576;
                       FStar_Syntax_Syntax.sigattrs = uu____12577;_},uu____12578),uu____12579),uu____12580,uu____12581,uu____12582)
                    when is_rec && (Prims.op_Negation (cfg.steps).zeta) -> no
                | (uu____12685,FStar_Pervasives_Native.Some
                   uu____12686,uu____12687,uu____12688) ->
                    (log_unfolding cfg
                       (fun uu____12756  ->
                          let uu____12757 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____12757);
                     (let uu____12758 =
                        let uu____12767 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12787 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____12787
                           in
                        let uu____12794 =
                          let uu____12803 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____12823 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____12823
                             in
                          let uu____12832 =
                            let uu____12841 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____12861 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____12861
                               in
                            [uu____12841]  in
                          uu____12803 :: uu____12832  in
                        uu____12767 :: uu____12794  in
                      comb_or uu____12758))
                | (uu____12892,uu____12893,FStar_Pervasives_Native.Some
                   uu____12894,uu____12895) ->
                    (log_unfolding cfg
                       (fun uu____12963  ->
                          let uu____12964 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____12964);
                     (let uu____12965 =
                        let uu____12974 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12994 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____12994
                           in
                        let uu____13001 =
                          let uu____13010 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____13030 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____13030
                             in
                          let uu____13039 =
                            let uu____13048 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____13068 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____13068
                               in
                            [uu____13048]  in
                          uu____13010 :: uu____13039  in
                        uu____12974 :: uu____13001  in
                      comb_or uu____12965))
                | (uu____13099,uu____13100,uu____13101,FStar_Pervasives_Native.Some
                   uu____13102) ->
                    (log_unfolding cfg
                       (fun uu____13170  ->
                          let uu____13171 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____13171);
                     (let uu____13172 =
                        let uu____13181 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____13201 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____13201
                           in
                        let uu____13208 =
                          let uu____13217 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____13237 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____13237
                             in
                          let uu____13246 =
                            let uu____13255 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____13275 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____13275
                               in
                            [uu____13255]  in
                          uu____13217 :: uu____13246  in
                        uu____13181 :: uu____13208  in
                      comb_or uu____13172))
                | uu____13306 ->
                    (log_unfolding cfg
                       (fun uu____13352  ->
                          let uu____13353 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          let uu____13354 =
                            FStar_Syntax_Print.delta_depth_to_string
                              fv.FStar_Syntax_Syntax.fv_delta
                             in
                          let uu____13355 =
                            FStar_Common.string_of_list
                              FStar_TypeChecker_Env.string_of_delta_level
                              cfg.delta_level
                             in
                          FStar_Util.print3
                            ">>> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                            uu____13353 uu____13354 uu____13355);
                     (let uu____13356 =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_Util.for_some
                             (fun uu___250_13360  ->
                                match uu___250_13360 with
                                | FStar_TypeChecker_Env.UnfoldTac  -> false
                                | FStar_TypeChecker_Env.NoDelta  -> false
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | FStar_TypeChecker_Env.Unfold l ->
                                    FStar_TypeChecker_Common.delta_depth_greater_than
                                      fv.FStar_Syntax_Syntax.fv_delta l))
                         in
                      FStar_All.pipe_left yesno uu____13356))
                 in
              log_unfolding cfg
                (fun uu____13373  ->
                   let uu____13374 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____13375 = FStar_Range.string_of_range rng  in
                   let uu____13376 = string_of_res res  in
                   FStar_Util.print3 ">>> For %s (%s), unfolding res = %s\n"
                     uu____13374 uu____13375 uu____13376);
              (match res with
               | (false ,uu____13385,uu____13386) ->
                   FStar_Pervasives_Native.None
               | (true ,false ,false ) ->
                   FStar_Pervasives_Native.Some (cfg, stack)
               | (true ,true ,false ) ->
                   let cfg' =
                     let uu___310_13402 = cfg  in
                     {
                       steps =
                         (let uu___311_13405 = cfg.steps  in
                          {
                            beta = (uu___311_13405.beta);
                            iota = false;
                            zeta = false;
                            weak = false;
                            hnf = false;
                            primops = false;
                            do_not_unfold_pure_lets =
                              (uu___311_13405.do_not_unfold_pure_lets);
                            unfold_until =
                              (FStar_Pervasives_Native.Some
                                 FStar_Syntax_Syntax.delta_constant);
                            unfold_only = FStar_Pervasives_Native.None;
                            unfold_fully = FStar_Pervasives_Native.None;
                            unfold_attr = (uu___311_13405.unfold_attr);
                            unfold_tac = (uu___311_13405.unfold_tac);
                            pure_subterms_within_computations =
                              (uu___311_13405.pure_subterms_within_computations);
                            simplify = false;
                            erase_universes =
                              (uu___311_13405.erase_universes);
                            allow_unbound_universes =
                              (uu___311_13405.allow_unbound_universes);
                            reify_ = (uu___311_13405.reify_);
                            compress_uvars = (uu___311_13405.compress_uvars);
                            no_full_norm = (uu___311_13405.no_full_norm);
                            check_no_uvars = (uu___311_13405.check_no_uvars);
                            unmeta = (uu___311_13405.unmeta);
                            unascribe = (uu___311_13405.unascribe);
                            in_full_norm_request =
                              (uu___311_13405.in_full_norm_request);
                            weakly_reduce_scrutinee =
                              (uu___311_13405.weakly_reduce_scrutinee)
                          });
                       tcenv = (uu___310_13402.tcenv);
                       debug = (uu___310_13402.debug);
                       delta_level = (uu___310_13402.delta_level);
                       primitive_steps = (uu___310_13402.primitive_steps);
                       strong = (uu___310_13402.strong);
                       memoize_lazy = (uu___310_13402.memoize_lazy);
                       normalize_pure_lets =
                         (uu___310_13402.normalize_pure_lets)
                     }  in
                   let stack' = (Cfg cfg) :: stack  in
                   FStar_Pervasives_Native.Some (cfg', stack')
               | (true ,false ,true ) ->
                   let uu____13421 =
                     let uu____13428 = FStar_List.tl stack  in
                     (cfg, uu____13428)  in
                   FStar_Pervasives_Native.Some uu____13421
               | uu____13439 ->
                   let uu____13446 =
                     let uu____13447 = string_of_res res  in
                     FStar_Util.format1 "Unexpected unfolding result: %s"
                       uu____13447
                      in
                   FStar_All.pipe_left failwith uu____13446)
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13755 ->
                   let uu____13780 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13780
               | uu____13781 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13789  ->
               let uu____13790 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13791 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13792 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13799 =
                 let uu____13800 =
                   let uu____13803 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13803
                    in
                 stack_to_string uu____13800  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13790 uu____13791 uu____13792 uu____13799);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13826 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13827 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13828 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13829;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____13830;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13833;
                 FStar_Syntax_Syntax.fv_delta = uu____13834;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13835;
                 FStar_Syntax_Syntax.fv_delta = uu____13836;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13837);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____13844 ->
               let uu____13851 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13851
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____13881 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____13881)
               ->
               let cfg' =
                 let uu___312_13883 = cfg  in
                 {
                   steps =
                     (let uu___313_13886 = cfg.steps  in
                      {
                        beta = (uu___313_13886.beta);
                        iota = (uu___313_13886.iota);
                        zeta = (uu___313_13886.zeta);
                        weak = (uu___313_13886.weak);
                        hnf = (uu___313_13886.hnf);
                        primops = (uu___313_13886.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___313_13886.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___313_13886.unfold_attr);
                        unfold_tac = (uu___313_13886.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___313_13886.pure_subterms_within_computations);
                        simplify = (uu___313_13886.simplify);
                        erase_universes = (uu___313_13886.erase_universes);
                        allow_unbound_universes =
                          (uu___313_13886.allow_unbound_universes);
                        reify_ = (uu___313_13886.reify_);
                        compress_uvars = (uu___313_13886.compress_uvars);
                        no_full_norm = (uu___313_13886.no_full_norm);
                        check_no_uvars = (uu___313_13886.check_no_uvars);
                        unmeta = (uu___313_13886.unmeta);
                        unascribe = (uu___313_13886.unascribe);
                        in_full_norm_request =
                          (uu___313_13886.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___313_13886.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___312_13883.tcenv);
                   debug = (uu___312_13883.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___312_13883.primitive_steps);
                   strong = (uu___312_13883.strong);
                   memoize_lazy = (uu___312_13883.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13891 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____13891 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____13920  ->
                              fun stack1  ->
                                match uu____13920 with
                                | (a,aq) ->
                                    let uu____13932 =
                                      let uu____13933 =
                                        let uu____13940 =
                                          let uu____13941 =
                                            let uu____13972 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____13972, false)  in
                                          Clos uu____13941  in
                                        (uu____13940, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____13933  in
                                    uu____13932 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14060  ->
                          let uu____14061 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14061);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14083 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___251_14088  ->
                                match uu___251_14088 with
                                | UnfoldUntil uu____14089 -> true
                                | UnfoldOnly uu____14090 -> true
                                | UnfoldFully uu____14093 -> true
                                | uu____14096 -> false))
                         in
                      if uu____14083
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___314_14101 = cfg  in
                      let uu____14102 =
                        let uu___315_14103 = to_fsteps s  in
                        {
                          beta = (uu___315_14103.beta);
                          iota = (uu___315_14103.iota);
                          zeta = (uu___315_14103.zeta);
                          weak = (uu___315_14103.weak);
                          hnf = (uu___315_14103.hnf);
                          primops = (uu___315_14103.primops);
                          do_not_unfold_pure_lets =
                            (uu___315_14103.do_not_unfold_pure_lets);
                          unfold_until = (uu___315_14103.unfold_until);
                          unfold_only = (uu___315_14103.unfold_only);
                          unfold_fully = (uu___315_14103.unfold_fully);
                          unfold_attr = (uu___315_14103.unfold_attr);
                          unfold_tac = (uu___315_14103.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___315_14103.pure_subterms_within_computations);
                          simplify = (uu___315_14103.simplify);
                          erase_universes = (uu___315_14103.erase_universes);
                          allow_unbound_universes =
                            (uu___315_14103.allow_unbound_universes);
                          reify_ = (uu___315_14103.reify_);
                          compress_uvars = (uu___315_14103.compress_uvars);
                          no_full_norm = (uu___315_14103.no_full_norm);
                          check_no_uvars = (uu___315_14103.check_no_uvars);
                          unmeta = (uu___315_14103.unmeta);
                          unascribe = (uu___315_14103.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___315_14103.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14102;
                        tcenv = (uu___314_14101.tcenv);
                        debug = (uu___314_14101.debug);
                        delta_level;
                        primitive_steps = (uu___314_14101.primitive_steps);
                        strong = (uu___314_14101.strong);
                        memoize_lazy = (uu___314_14101.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14108 =
                          let uu____14109 =
                            let uu____14114 = FStar_Util.now ()  in
                            (t1, uu____14114)  in
                          Debug uu____14109  in
                        uu____14108 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14118 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14118
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14127 =
                      let uu____14134 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14134, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14127  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14144 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14144  in
               let uu____14145 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14145 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14173 = lookup_bvar env x  in
               (match uu____14173 with
                | Univ uu____14174 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14223 = FStar_ST.op_Bang r  in
                      (match uu____14223 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14345  ->
                                 let uu____14346 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14347 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14346
                                   uu____14347);
                            (let uu____14348 = maybe_weakly_reduced t'  in
                             if uu____14348
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14349 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14420)::uu____14421 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14431,uu____14432))::stack_rest ->
                    (match c with
                     | Univ uu____14436 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14445 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14466  ->
                                    let uu____14467 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14467);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14495  ->
                                    let uu____14496 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14496);
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
                       (fun uu____14562  ->
                          let uu____14563 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14563);
                     norm cfg env stack1 t1)
                | (Match uu____14564)::uu____14565 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14579 = cfg.steps  in
                             {
                               beta = (uu___316_14579.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14579.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14579.unfold_until);
                               unfold_only = (uu___316_14579.unfold_only);
                               unfold_fully = (uu___316_14579.unfold_fully);
                               unfold_attr = (uu___316_14579.unfold_attr);
                               unfold_tac = (uu___316_14579.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14579.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14579.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14579.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14579.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14579.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14579.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14581 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14581.tcenv);
                               debug = (uu___317_14581.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14581.primitive_steps);
                               strong = (uu___317_14581.strong);
                               memoize_lazy = (uu___317_14581.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14581.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14583 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14583 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14615  -> dummy :: env1) env)
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
                                          let uu____14656 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14656)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_14663 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_14663.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_14663.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14664 -> lopt  in
                           (log cfg
                              (fun uu____14670  ->
                                 let uu____14671 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14671);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_14680 = cfg  in
                               {
                                 steps = (uu___319_14680.steps);
                                 tcenv = (uu___319_14680.tcenv);
                                 debug = (uu___319_14680.debug);
                                 delta_level = (uu___319_14680.delta_level);
                                 primitive_steps =
                                   (uu___319_14680.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_14680.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_14680.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____14683)::uu____14684 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14694 = cfg.steps  in
                             {
                               beta = (uu___316_14694.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14694.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14694.unfold_until);
                               unfold_only = (uu___316_14694.unfold_only);
                               unfold_fully = (uu___316_14694.unfold_fully);
                               unfold_attr = (uu___316_14694.unfold_attr);
                               unfold_tac = (uu___316_14694.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14694.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14694.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14694.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14694.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14694.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14694.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14696 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14696.tcenv);
                               debug = (uu___317_14696.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14696.primitive_steps);
                               strong = (uu___317_14696.strong);
                               memoize_lazy = (uu___317_14696.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14696.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14698 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14698 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14730  -> dummy :: env1) env)
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
                                          let uu____14771 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14771)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_14778 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_14778.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_14778.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14779 -> lopt  in
                           (log cfg
                              (fun uu____14785  ->
                                 let uu____14786 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14786);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_14795 = cfg  in
                               {
                                 steps = (uu___319_14795.steps);
                                 tcenv = (uu___319_14795.tcenv);
                                 debug = (uu___319_14795.debug);
                                 delta_level = (uu___319_14795.delta_level);
                                 primitive_steps =
                                   (uu___319_14795.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_14795.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_14795.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14798)::uu____14799 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14811 = cfg.steps  in
                             {
                               beta = (uu___316_14811.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14811.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14811.unfold_until);
                               unfold_only = (uu___316_14811.unfold_only);
                               unfold_fully = (uu___316_14811.unfold_fully);
                               unfold_attr = (uu___316_14811.unfold_attr);
                               unfold_tac = (uu___316_14811.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14811.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14811.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14811.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14811.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14811.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14811.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14813 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14813.tcenv);
                               debug = (uu___317_14813.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14813.primitive_steps);
                               strong = (uu___317_14813.strong);
                               memoize_lazy = (uu___317_14813.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14813.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14815 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14815 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14847  -> dummy :: env1) env)
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
                                          let uu____14888 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14888)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_14895 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_14895.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_14895.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14896 -> lopt  in
                           (log cfg
                              (fun uu____14902  ->
                                 let uu____14903 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14903);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_14912 = cfg  in
                               {
                                 steps = (uu___319_14912.steps);
                                 tcenv = (uu___319_14912.tcenv);
                                 debug = (uu___319_14912.debug);
                                 delta_level = (uu___319_14912.delta_level);
                                 primitive_steps =
                                   (uu___319_14912.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_14912.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_14912.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14915)::uu____14916 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14930 = cfg.steps  in
                             {
                               beta = (uu___316_14930.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14930.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14930.unfold_until);
                               unfold_only = (uu___316_14930.unfold_only);
                               unfold_fully = (uu___316_14930.unfold_fully);
                               unfold_attr = (uu___316_14930.unfold_attr);
                               unfold_tac = (uu___316_14930.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14930.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14930.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14930.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14930.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14930.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14930.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14932 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14932.tcenv);
                               debug = (uu___317_14932.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14932.primitive_steps);
                               strong = (uu___317_14932.strong);
                               memoize_lazy = (uu___317_14932.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14932.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14934 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14934 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14966  -> dummy :: env1) env)
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
                                          let uu____15007 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15007)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15014 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15014.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15014.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15015 -> lopt  in
                           (log cfg
                              (fun uu____15021  ->
                                 let uu____15022 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15022);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15031 = cfg  in
                               {
                                 steps = (uu___319_15031.steps);
                                 tcenv = (uu___319_15031.tcenv);
                                 debug = (uu___319_15031.debug);
                                 delta_level = (uu___319_15031.delta_level);
                                 primitive_steps =
                                   (uu___319_15031.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15031.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15031.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15034)::uu____15035 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_15049 = cfg.steps  in
                             {
                               beta = (uu___316_15049.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_15049.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_15049.unfold_until);
                               unfold_only = (uu___316_15049.unfold_only);
                               unfold_fully = (uu___316_15049.unfold_fully);
                               unfold_attr = (uu___316_15049.unfold_attr);
                               unfold_tac = (uu___316_15049.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_15049.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_15049.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_15049.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_15049.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_15049.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_15049.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_15051 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_15051.tcenv);
                               debug = (uu___317_15051.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_15051.primitive_steps);
                               strong = (uu___317_15051.strong);
                               memoize_lazy = (uu___317_15051.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_15051.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15053 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15053 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15085  -> dummy :: env1) env)
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
                                          let uu____15126 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15126)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15133 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15133.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15133.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15134 -> lopt  in
                           (log cfg
                              (fun uu____15140  ->
                                 let uu____15141 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15141);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15150 = cfg  in
                               {
                                 steps = (uu___319_15150.steps);
                                 tcenv = (uu___319_15150.tcenv);
                                 debug = (uu___319_15150.debug);
                                 delta_level = (uu___319_15150.delta_level);
                                 primitive_steps =
                                   (uu___319_15150.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15150.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15150.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15153)::uu____15154 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_15172 = cfg.steps  in
                             {
                               beta = (uu___316_15172.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_15172.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_15172.unfold_until);
                               unfold_only = (uu___316_15172.unfold_only);
                               unfold_fully = (uu___316_15172.unfold_fully);
                               unfold_attr = (uu___316_15172.unfold_attr);
                               unfold_tac = (uu___316_15172.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_15172.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_15172.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_15172.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_15172.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_15172.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_15172.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_15174 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_15174.tcenv);
                               debug = (uu___317_15174.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_15174.primitive_steps);
                               strong = (uu___317_15174.strong);
                               memoize_lazy = (uu___317_15174.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_15174.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15176 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15176 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15208  -> dummy :: env1) env)
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
                                          let uu____15249 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15249)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15256 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15256.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15256.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15257 -> lopt  in
                           (log cfg
                              (fun uu____15263  ->
                                 let uu____15264 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15264);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15273 = cfg  in
                               {
                                 steps = (uu___319_15273.steps);
                                 tcenv = (uu___319_15273.tcenv);
                                 debug = (uu___319_15273.debug);
                                 delta_level = (uu___319_15273.delta_level);
                                 primitive_steps =
                                   (uu___319_15273.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15273.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15273.normalize_pure_lets)
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
                             let uu___316_15279 = cfg.steps  in
                             {
                               beta = (uu___316_15279.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_15279.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_15279.unfold_until);
                               unfold_only = (uu___316_15279.unfold_only);
                               unfold_fully = (uu___316_15279.unfold_fully);
                               unfold_attr = (uu___316_15279.unfold_attr);
                               unfold_tac = (uu___316_15279.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_15279.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_15279.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_15279.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_15279.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_15279.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_15279.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_15281 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_15281.tcenv);
                               debug = (uu___317_15281.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_15281.primitive_steps);
                               strong = (uu___317_15281.strong);
                               memoize_lazy = (uu___317_15281.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_15281.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15283 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15283 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15315  -> dummy :: env1) env)
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
                                          let uu____15356 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15356)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15363 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15363.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15363.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15364 -> lopt  in
                           (log cfg
                              (fun uu____15370  ->
                                 let uu____15371 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15371);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15380 = cfg  in
                               {
                                 steps = (uu___319_15380.steps);
                                 tcenv = (uu___319_15380.tcenv);
                                 debug = (uu___319_15380.debug);
                                 delta_level = (uu___319_15380.delta_level);
                                 primitive_steps =
                                   (uu___319_15380.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15380.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15380.normalize_pure_lets)
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
                      (fun uu____15419  ->
                         fun stack1  ->
                           match uu____15419 with
                           | (a,aq) ->
                               let uu____15431 =
                                 let uu____15432 =
                                   let uu____15439 =
                                     let uu____15440 =
                                       let uu____15471 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15471, false)  in
                                     Clos uu____15440  in
                                   (uu____15439, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15432  in
                               uu____15431 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15559  ->
                     let uu____15560 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15560);
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
                             ((let uu___320_15606 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___320_15606.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___320_15606.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15607 ->
                      let uu____15622 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15622)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15625 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15625 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15650 =
                          let uu____15651 =
                            let uu____15658 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___321_15664 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___321_15664.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___321_15664.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15658)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15651  in
                        mk uu____15650 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15683 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15683
               else
                 (let uu____15685 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15685 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15693 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15715  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15693 c1  in
                      let t2 =
                        let uu____15737 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15737 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15848)::uu____15849 ->
                    (log cfg
                       (fun uu____15862  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15863)::uu____15864 ->
                    (log cfg
                       (fun uu____15875  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15876,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15877;
                                   FStar_Syntax_Syntax.vars = uu____15878;_},uu____15879,uu____15880))::uu____15881
                    ->
                    (log cfg
                       (fun uu____15888  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15889)::uu____15890 ->
                    (log cfg
                       (fun uu____15901  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15902 ->
                    (log cfg
                       (fun uu____15905  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15909  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15934 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15934
                         | FStar_Util.Inr c ->
                             let uu____15948 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____15948
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____15971 =
                               let uu____15972 =
                                 let uu____15999 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____15999, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15972
                                in
                             mk uu____15971 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16034 ->
                           let uu____16035 =
                             let uu____16036 =
                               let uu____16037 =
                                 let uu____16064 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16064, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16037
                                in
                             mk uu____16036 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16035))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___322_16141 = cfg  in
                   {
                     steps =
                       (let uu___323_16144 = cfg.steps  in
                        {
                          beta = (uu___323_16144.beta);
                          iota = (uu___323_16144.iota);
                          zeta = (uu___323_16144.zeta);
                          weak = true;
                          hnf = (uu___323_16144.hnf);
                          primops = (uu___323_16144.primops);
                          do_not_unfold_pure_lets =
                            (uu___323_16144.do_not_unfold_pure_lets);
                          unfold_until = (uu___323_16144.unfold_until);
                          unfold_only = (uu___323_16144.unfold_only);
                          unfold_fully = (uu___323_16144.unfold_fully);
                          unfold_attr = (uu___323_16144.unfold_attr);
                          unfold_tac = (uu___323_16144.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___323_16144.pure_subterms_within_computations);
                          simplify = (uu___323_16144.simplify);
                          erase_universes = (uu___323_16144.erase_universes);
                          allow_unbound_universes =
                            (uu___323_16144.allow_unbound_universes);
                          reify_ = (uu___323_16144.reify_);
                          compress_uvars = (uu___323_16144.compress_uvars);
                          no_full_norm = (uu___323_16144.no_full_norm);
                          check_no_uvars = (uu___323_16144.check_no_uvars);
                          unmeta = (uu___323_16144.unmeta);
                          unascribe = (uu___323_16144.unascribe);
                          in_full_norm_request =
                            (uu___323_16144.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___323_16144.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___322_16141.tcenv);
                     debug = (uu___322_16141.debug);
                     delta_level = (uu___322_16141.delta_level);
                     primitive_steps = (uu___322_16141.primitive_steps);
                     strong = (uu___322_16141.strong);
                     memoize_lazy = (uu___322_16141.memoize_lazy);
                     normalize_pure_lets =
                       (uu___322_16141.normalize_pure_lets)
                   }  in
                 norm cfg' env ((Cfg cfg) :: stack1) head1
               else norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____16180 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16180 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___324_16200 = cfg  in
                               let uu____16201 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___324_16200.steps);
                                 tcenv = uu____16201;
                                 debug = (uu___324_16200.debug);
                                 delta_level = (uu___324_16200.delta_level);
                                 primitive_steps =
                                   (uu___324_16200.primitive_steps);
                                 strong = (uu___324_16200.strong);
                                 memoize_lazy = (uu___324_16200.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___324_16200.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16208 =
                                 let uu____16209 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16209  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16208
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___325_16212 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___325_16212.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___325_16212.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___325_16212.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___325_16212.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16213 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16213
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16224,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16225;
                               FStar_Syntax_Syntax.lbunivs = uu____16226;
                               FStar_Syntax_Syntax.lbtyp = uu____16227;
                               FStar_Syntax_Syntax.lbeff = uu____16228;
                               FStar_Syntax_Syntax.lbdef = uu____16229;
                               FStar_Syntax_Syntax.lbattrs = uu____16230;
                               FStar_Syntax_Syntax.lbpos = uu____16231;_}::uu____16232),uu____16233)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16273 =
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
               if uu____16273
               then
                 let binder =
                   let uu____16275 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16275  in
                 let env1 =
                   let uu____16285 =
                     let uu____16292 =
                       let uu____16293 =
                         let uu____16324 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16324,
                           false)
                          in
                       Clos uu____16293  in
                     ((FStar_Pervasives_Native.Some binder), uu____16292)  in
                   uu____16285 :: env  in
                 (log cfg
                    (fun uu____16419  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16423  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16424 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16424))
                 else
                   (let uu____16426 =
                      let uu____16431 =
                        let uu____16432 =
                          let uu____16437 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16437
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16432]  in
                      FStar_Syntax_Subst.open_term uu____16431 body  in
                    match uu____16426 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16458  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16466 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16466  in
                            FStar_Util.Inl
                              (let uu___326_16476 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___326_16476.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___326_16476.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16479  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___327_16481 = lb  in
                             let uu____16482 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___327_16481.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___327_16481.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16482;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___327_16481.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___327_16481.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16507  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___328_16530 = cfg  in
                             {
                               steps = (uu___328_16530.steps);
                               tcenv = (uu___328_16530.tcenv);
                               debug = (uu___328_16530.debug);
                               delta_level = (uu___328_16530.delta_level);
                               primitive_steps =
                                 (uu___328_16530.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___328_16530.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___328_16530.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16533  ->
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
               let uu____16550 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16550 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16586 =
                               let uu___329_16587 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___329_16587.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___329_16587.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16586  in
                           let uu____16588 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16588 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16614 =
                                   FStar_List.map (fun uu____16630  -> dummy)
                                     lbs1
                                    in
                                 let uu____16631 =
                                   let uu____16640 =
                                     FStar_List.map
                                       (fun uu____16660  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16640 env  in
                                 FStar_List.append uu____16614 uu____16631
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16684 =
                                       let uu___330_16685 = rc  in
                                       let uu____16686 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___330_16685.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16686;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___330_16685.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16684
                                 | uu____16695 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___331_16701 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___331_16701.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___331_16701.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___331_16701.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___331_16701.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16711 =
                        FStar_List.map (fun uu____16727  -> dummy) lbs2  in
                      FStar_List.append uu____16711 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16735 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16735 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___332_16751 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___332_16751.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___332_16751.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16780 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16780
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16799 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16875  ->
                        match uu____16875 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___333_16996 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___333_16996.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___333_16996.FStar_Syntax_Syntax.sort)
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
               (match uu____16799 with
                | (rec_env,memos,uu____17223) ->
                    let uu____17276 =
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
                             let uu____17599 =
                               let uu____17606 =
                                 let uu____17607 =
                                   let uu____17638 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17638, false)
                                    in
                                 Clos uu____17607  in
                               (FStar_Pervasives_Native.None, uu____17606)
                                in
                             uu____17599 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17742  ->
                     let uu____17743 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17743);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____17765 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17767::uu____17768 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17773) ->
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
                             | uu____17796 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17810 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17810
                              | uu____17821 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17827 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17853 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17869 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17884 =
                        let uu____17885 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17886 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17885 uu____17886
                         in
                      failwith uu____17884
                    else
                      (let uu____17888 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____17888)
                | uu____17889 -> norm cfg env stack t2))

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
                let uu____17899 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____17899  in
              let uu____17900 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17900 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____17913  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____17924  ->
                        let uu____17925 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17926 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____17925 uu____17926);
                   (let t1 =
                      if
                        (cfg.steps).unfold_until =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        (let uu____17931 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____17931 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____17940))::stack1 ->
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
                      | uu____17979 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____17982 ->
                          let uu____17985 =
                            let uu____17986 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17986
                             in
                          failwith uu____17985
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
                  let uu___334_18010 = cfg  in
                  let uu____18011 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18011;
                    tcenv = (uu___334_18010.tcenv);
                    debug = (uu___334_18010.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___334_18010.primitive_steps);
                    strong = (uu___334_18010.strong);
                    memoize_lazy = (uu___334_18010.memoize_lazy);
                    normalize_pure_lets =
                      (uu___334_18010.normalize_pure_lets)
                  }
                else
                  (let uu___335_18013 = cfg  in
                   {
                     steps =
                       (let uu___336_18016 = cfg.steps  in
                        {
                          beta = (uu___336_18016.beta);
                          iota = (uu___336_18016.iota);
                          zeta = false;
                          weak = (uu___336_18016.weak);
                          hnf = (uu___336_18016.hnf);
                          primops = (uu___336_18016.primops);
                          do_not_unfold_pure_lets =
                            (uu___336_18016.do_not_unfold_pure_lets);
                          unfold_until = (uu___336_18016.unfold_until);
                          unfold_only = (uu___336_18016.unfold_only);
                          unfold_fully = (uu___336_18016.unfold_fully);
                          unfold_attr = (uu___336_18016.unfold_attr);
                          unfold_tac = (uu___336_18016.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___336_18016.pure_subterms_within_computations);
                          simplify = (uu___336_18016.simplify);
                          erase_universes = (uu___336_18016.erase_universes);
                          allow_unbound_universes =
                            (uu___336_18016.allow_unbound_universes);
                          reify_ = (uu___336_18016.reify_);
                          compress_uvars = (uu___336_18016.compress_uvars);
                          no_full_norm = (uu___336_18016.no_full_norm);
                          check_no_uvars = (uu___336_18016.check_no_uvars);
                          unmeta = (uu___336_18016.unmeta);
                          unascribe = (uu___336_18016.unascribe);
                          in_full_norm_request =
                            (uu___336_18016.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___336_18016.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___335_18013.tcenv);
                     debug = (uu___335_18013.debug);
                     delta_level = (uu___335_18013.delta_level);
                     primitive_steps = (uu___335_18013.primitive_steps);
                     strong = (uu___335_18013.strong);
                     memoize_lazy = (uu___335_18013.memoize_lazy);
                     normalize_pure_lets =
                       (uu___335_18013.normalize_pure_lets)
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
                  (fun uu____18050  ->
                     let uu____18051 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18052 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18051
                       uu____18052);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18054 =
                   let uu____18055 = FStar_Syntax_Subst.compress head3  in
                   uu____18055.FStar_Syntax_Syntax.n  in
                 match uu____18054 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18073 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18073
                        in
                     let uu____18074 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18074 with
                      | (uu____18075,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18085 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18095 =
                                   let uu____18096 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18096.FStar_Syntax_Syntax.n  in
                                 match uu____18095 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18102,uu____18103))
                                     ->
                                     let uu____18112 =
                                       let uu____18113 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18113.FStar_Syntax_Syntax.n  in
                                     (match uu____18112 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18119,msrc,uu____18121))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18130 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18130
                                      | uu____18131 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18132 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18133 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18133 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___337_18138 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___337_18138.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___337_18138.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___337_18138.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___337_18138.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___337_18138.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18139 = FStar_List.tl stack  in
                                    let uu____18140 =
                                      let uu____18141 =
                                        let uu____18148 =
                                          let uu____18149 =
                                            let uu____18162 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18162)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18149
                                           in
                                        FStar_Syntax_Syntax.mk uu____18148
                                         in
                                      uu____18141
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18139 uu____18140
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18178 =
                                      let uu____18179 = is_return body  in
                                      match uu____18179 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18183;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18184;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18187 -> false  in
                                    if uu____18178
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
                                         let uu____18208 =
                                           let uu____18215 =
                                             let uu____18216 =
                                               let uu____18233 =
                                                 let uu____18240 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18240]  in
                                               (uu____18233, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18216
                                              in
                                           FStar_Syntax_Syntax.mk uu____18215
                                            in
                                         uu____18208
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18274 =
                                           let uu____18275 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18275.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18274 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18281::uu____18282::[])
                                             ->
                                             let uu____18287 =
                                               let uu____18294 =
                                                 let uu____18295 =
                                                   let uu____18302 =
                                                     let uu____18303 =
                                                       let uu____18304 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18304
                                                        in
                                                     let uu____18305 =
                                                       let uu____18308 =
                                                         let uu____18309 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18309
                                                          in
                                                       [uu____18308]  in
                                                     uu____18303 ::
                                                       uu____18305
                                                      in
                                                   (bind1, uu____18302)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18295
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18294
                                                in
                                             uu____18287
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18315 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18327 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18327
                                         then
                                           let uu____18336 =
                                             let uu____18343 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18343
                                              in
                                           let uu____18344 =
                                             let uu____18353 =
                                               let uu____18360 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18360
                                                in
                                             [uu____18353]  in
                                           uu____18336 :: uu____18344
                                         else []  in
                                       let reified =
                                         let uu____18389 =
                                           let uu____18396 =
                                             let uu____18397 =
                                               let uu____18412 =
                                                 let uu____18421 =
                                                   let uu____18430 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18437 =
                                                     let uu____18446 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18446]  in
                                                   uu____18430 :: uu____18437
                                                    in
                                                 let uu____18471 =
                                                   let uu____18480 =
                                                     let uu____18489 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18496 =
                                                       let uu____18505 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18512 =
                                                         let uu____18521 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18528 =
                                                           let uu____18537 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18537]  in
                                                         uu____18521 ::
                                                           uu____18528
                                                          in
                                                       uu____18505 ::
                                                         uu____18512
                                                        in
                                                     uu____18489 ::
                                                       uu____18496
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18480
                                                    in
                                                 FStar_List.append
                                                   uu____18421 uu____18471
                                                  in
                                               (bind_inst, uu____18412)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18397
                                              in
                                           FStar_Syntax_Syntax.mk uu____18396
                                            in
                                         uu____18389
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18603  ->
                                            let uu____18604 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18605 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18604 uu____18605);
                                       (let uu____18606 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18606 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18630 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18630
                        in
                     let uu____18631 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18631 with
                      | (uu____18632,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18669 =
                                  let uu____18670 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18670.FStar_Syntax_Syntax.n  in
                                match uu____18669 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18674) -> t2
                                | uu____18679 -> head4  in
                              let uu____18680 =
                                let uu____18681 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18681.FStar_Syntax_Syntax.n  in
                              match uu____18680 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18687 -> FStar_Pervasives_Native.None
                               in
                            let uu____18688 = maybe_extract_fv head4  in
                            match uu____18688 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18698 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18698
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18703 = maybe_extract_fv head5
                                     in
                                  match uu____18703 with
                                  | FStar_Pervasives_Native.Some uu____18708
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18709 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18714 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18729 =
                              match uu____18729 with
                              | (e,q) ->
                                  let uu____18736 =
                                    let uu____18737 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18737.FStar_Syntax_Syntax.n  in
                                  (match uu____18736 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____18752 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____18752
                                   | uu____18753 -> false)
                               in
                            let uu____18754 =
                              let uu____18755 =
                                let uu____18764 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18764 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18755
                               in
                            if uu____18754
                            then
                              let uu____18783 =
                                let uu____18784 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18784
                                 in
                              failwith uu____18783
                            else ());
                           (let uu____18786 = maybe_unfold_action head_app
                               in
                            match uu____18786 with
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
                                   (fun uu____18829  ->
                                      let uu____18830 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18831 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18830 uu____18831);
                                 (let uu____18832 = FStar_List.tl stack  in
                                  norm cfg env uu____18832 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18834) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18858 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18858  in
                     (log cfg
                        (fun uu____18862  ->
                           let uu____18863 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18863);
                      (let uu____18864 = FStar_List.tl stack  in
                       norm cfg env uu____18864 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18985  ->
                               match uu____18985 with
                               | (pat,wopt,tm) ->
                                   let uu____19033 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19033)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19065 = FStar_List.tl stack  in
                     norm cfg env uu____19065 tm
                 | uu____19066 -> fallback ())

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
              (fun uu____19080  ->
                 let uu____19081 = FStar_Ident.string_of_lid msrc  in
                 let uu____19082 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19083 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19081
                   uu____19082 uu____19083);
            (let uu____19084 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19084
             then
               let ed =
                 let uu____19086 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19086  in
               let uu____19087 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19087 with
               | (uu____19088,return_repr) ->
                   let return_inst =
                     let uu____19101 =
                       let uu____19102 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19102.FStar_Syntax_Syntax.n  in
                     match uu____19101 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19108::[]) ->
                         let uu____19113 =
                           let uu____19120 =
                             let uu____19121 =
                               let uu____19128 =
                                 let uu____19129 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19129]  in
                               (return_tm, uu____19128)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19121  in
                           FStar_Syntax_Syntax.mk uu____19120  in
                         uu____19113 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19135 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19138 =
                     let uu____19145 =
                       let uu____19146 =
                         let uu____19161 =
                           let uu____19170 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19177 =
                             let uu____19186 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19186]  in
                           uu____19170 :: uu____19177  in
                         (return_inst, uu____19161)  in
                       FStar_Syntax_Syntax.Tm_app uu____19146  in
                     FStar_Syntax_Syntax.mk uu____19145  in
                   uu____19138 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19225 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19225 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19228 =
                      let uu____19229 = FStar_Ident.text_of_lid msrc  in
                      let uu____19230 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19229 uu____19230
                       in
                    failwith uu____19228
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19231;
                      FStar_TypeChecker_Env.mtarget = uu____19232;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19233;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19255 =
                      let uu____19256 = FStar_Ident.text_of_lid msrc  in
                      let uu____19257 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19256 uu____19257
                       in
                    failwith uu____19255
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19258;
                      FStar_TypeChecker_Env.mtarget = uu____19259;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19260;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____19295 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____19296 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____19295 t FStar_Syntax_Syntax.tun uu____19296))

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
                (fun uu____19352  ->
                   match uu____19352 with
                   | (a,imp) ->
                       let uu____19363 = norm cfg env [] a  in
                       (uu____19363, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____19371  ->
             let uu____19372 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____19373 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____19372 uu____19373);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19397 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____19397
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___338_19400 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___338_19400.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___338_19400.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19422 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____19422
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___339_19425 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___339_19425.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___339_19425.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____19462  ->
                      match uu____19462 with
                      | (a,i) ->
                          let uu____19473 = norm cfg env [] a  in
                          (uu____19473, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___252_19491  ->
                       match uu___252_19491 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____19495 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____19495
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___340_19503 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___341_19506 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___341_19506.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___340_19503.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___340_19503.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19509  ->
        match uu____19509 with
        | (x,imp) ->
            let uu____19512 =
              let uu___342_19513 = x  in
              let uu____19514 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___342_19513.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___342_19513.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19514
              }  in
            (uu____19512, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19520 =
          FStar_List.fold_left
            (fun uu____19554  ->
               fun b  ->
                 match uu____19554 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19520 with | (nbs,uu____19634) -> FStar_List.rev nbs

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
            let uu____19666 =
              let uu___343_19667 = rc  in
              let uu____19668 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___343_19667.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19668;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___343_19667.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19666
        | uu____19677 -> lopt

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
            (let uu____19698 = FStar_Syntax_Print.term_to_string tm  in
             let uu____19699 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____19698
               uu____19699)
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
          let uu____19721 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____19721
          then tm1
          else
            (let w t =
               let uu___344_19735 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___344_19735.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___344_19735.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____19746 =
                 let uu____19747 = FStar_Syntax_Util.unmeta t  in
                 uu____19747.FStar_Syntax_Syntax.n  in
               match uu____19746 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____19754 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____19803)::args1,(bv,uu____19806)::bs1) ->
                   let uu____19840 =
                     let uu____19841 = FStar_Syntax_Subst.compress t  in
                     uu____19841.FStar_Syntax_Syntax.n  in
                   (match uu____19840 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____19845 -> false)
               | ([],[]) -> true
               | (uu____19866,uu____19867) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19908 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19909 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____19908
                    uu____19909)
               else ();
               (let uu____19911 = FStar_Syntax_Util.head_and_args' t  in
                match uu____19911 with
                | (hd1,args) ->
                    let uu____19944 =
                      let uu____19945 = FStar_Syntax_Subst.compress hd1  in
                      uu____19945.FStar_Syntax_Syntax.n  in
                    (match uu____19944 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____19952 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____19953 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____19954 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____19952 uu____19953 uu____19954)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____19956 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19973 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19974 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____19973
                    uu____19974)
               else ();
               (let uu____19976 = FStar_Syntax_Util.is_squash t  in
                match uu____19976 with
                | FStar_Pervasives_Native.Some (uu____19987,t') ->
                    is_applied bs t'
                | uu____19999 ->
                    let uu____20008 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____20008 with
                     | FStar_Pervasives_Native.Some (uu____20019,t') ->
                         is_applied bs t'
                     | uu____20031 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20055 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20055 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20062)::(q,uu____20064)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20092 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20093 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20092 uu____20093)
                    else ();
                    (let uu____20095 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20095 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20100 =
                           let uu____20101 = FStar_Syntax_Subst.compress p
                              in
                           uu____20101.FStar_Syntax_Syntax.n  in
                         (match uu____20100 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20109 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20109))
                          | uu____20112 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20115)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20132 =
                           let uu____20133 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20133.FStar_Syntax_Syntax.n  in
                         (match uu____20132 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20141 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20141))
                          | uu____20144 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20148 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20148 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20153 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20153 with
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
                                     let uu____20164 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20164))
                               | uu____20167 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____20172)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____20189 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____20189 with
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
                                     let uu____20200 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20200))
                               | uu____20203 -> FStar_Pervasives_Native.None)
                          | uu____20206 -> FStar_Pervasives_Native.None)
                     | uu____20209 -> FStar_Pervasives_Native.None))
               | uu____20212 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____20225 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20225 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____20231)::[],uu____20232,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20243 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____20244 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____20243
                         uu____20244)
                    else ();
                    is_quantified_const bv phi')
               | uu____20246 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____20259 =
                 let uu____20260 = FStar_Syntax_Subst.compress phi  in
                 uu____20260.FStar_Syntax_Syntax.n  in
               match uu____20259 with
               | FStar_Syntax_Syntax.Tm_match (uu____20265,br::brs) ->
                   let uu____20332 = br  in
                   (match uu____20332 with
                    | (uu____20349,uu____20350,e) ->
                        let r =
                          let uu____20371 = simp_t e  in
                          match uu____20371 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____20377 =
                                FStar_List.for_all
                                  (fun uu____20395  ->
                                     match uu____20395 with
                                     | (uu____20408,uu____20409,e') ->
                                         let uu____20423 = simp_t e'  in
                                         uu____20423 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____20377
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____20431 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____20440 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____20440
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____20471 =
                 match uu____20471 with
                 | (t1,q) ->
                     let uu____20484 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____20484 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____20512 -> (t1, q))
                  in
               let uu____20523 = FStar_Syntax_Util.head_and_args t  in
               match uu____20523 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____20589 =
                 let uu____20590 = FStar_Syntax_Util.unmeta ty  in
                 uu____20590.FStar_Syntax_Syntax.n  in
               match uu____20589 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____20594) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____20599,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____20619 -> false  in
             let simplify1 arg =
               let uu____20644 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____20644, arg)  in
             let uu____20653 = is_forall_const tm1  in
             match uu____20653 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____20658 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____20659 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____20658
                       uu____20659)
                  else ();
                  (let uu____20661 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____20661))
             | FStar_Pervasives_Native.None  ->
                 let uu____20662 =
                   let uu____20663 = FStar_Syntax_Subst.compress tm1  in
                   uu____20663.FStar_Syntax_Syntax.n  in
                 (match uu____20662 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____20667;
                              FStar_Syntax_Syntax.vars = uu____20668;_},uu____20669);
                         FStar_Syntax_Syntax.pos = uu____20670;
                         FStar_Syntax_Syntax.vars = uu____20671;_},args)
                      ->
                      let uu____20697 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20697
                      then
                        let uu____20698 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20698 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20743)::
                             (uu____20744,(arg,uu____20746))::[] ->
                             maybe_auto_squash arg
                         | (uu____20795,(arg,uu____20797))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20798)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20847)::uu____20848::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20899::(FStar_Pervasives_Native.Some (false
                                         ),uu____20900)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20951 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20965 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20965
                         then
                           let uu____20966 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20966 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21011)::uu____21012::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21063::(FStar_Pervasives_Native.Some (true
                                           ),uu____21064)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21115)::(uu____21116,(arg,uu____21118))::[]
                               -> maybe_auto_squash arg
                           | (uu____21167,(arg,uu____21169))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21170)::[]
                               -> maybe_auto_squash arg
                           | uu____21219 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21233 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21233
                            then
                              let uu____21234 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21234 with
                              | uu____21279::(FStar_Pervasives_Native.Some
                                              (true ),uu____21280)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21331)::uu____21332::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21383)::(uu____21384,(arg,uu____21386))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21435,(p,uu____21437))::(uu____21438,
                                                                (q,uu____21440))::[]
                                  ->
                                  let uu____21487 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21487
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21489 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21503 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21503
                               then
                                 let uu____21504 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21504 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21549)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21550)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21601)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21602)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21653)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21654)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21705)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21706)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21757,(arg,uu____21759))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21760)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21809)::(uu____21810,(arg,uu____21812))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21861,(arg,uu____21863))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21864)::[]
                                     ->
                                     let uu____21913 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21913
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21914)::(uu____21915,(arg,uu____21917))::[]
                                     ->
                                     let uu____21966 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21966
                                 | (uu____21967,(p,uu____21969))::(uu____21970,
                                                                   (q,uu____21972))::[]
                                     ->
                                     let uu____22019 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22019
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22021 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22035 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22035
                                  then
                                    let uu____22036 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22036 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22081)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22112)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22143 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22157 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22157
                                     then
                                       match args with
                                       | (t,uu____22159)::[] ->
                                           let uu____22176 =
                                             let uu____22177 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22177.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22176 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22180::[],body,uu____22182)
                                                ->
                                                let uu____22209 = simp_t body
                                                   in
                                                (match uu____22209 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22212 -> tm1)
                                            | uu____22215 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22217))::(t,uu____22219)::[]
                                           ->
                                           let uu____22246 =
                                             let uu____22247 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22247.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22246 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22250::[],body,uu____22252)
                                                ->
                                                let uu____22279 = simp_t body
                                                   in
                                                (match uu____22279 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22282 -> tm1)
                                            | uu____22285 -> tm1)
                                       | uu____22286 -> tm1
                                     else
                                       (let uu____22296 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22296
                                        then
                                          match args with
                                          | (t,uu____22298)::[] ->
                                              let uu____22315 =
                                                let uu____22316 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22316.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22315 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22319::[],body,uu____22321)
                                                   ->
                                                   let uu____22348 =
                                                     simp_t body  in
                                                   (match uu____22348 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22351 -> tm1)
                                               | uu____22354 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22356))::(t,uu____22358)::[]
                                              ->
                                              let uu____22385 =
                                                let uu____22386 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22386.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22385 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22389::[],body,uu____22391)
                                                   ->
                                                   let uu____22418 =
                                                     simp_t body  in
                                                   (match uu____22418 with
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
                                                    | uu____22421 -> tm1)
                                               | uu____22424 -> tm1)
                                          | uu____22425 -> tm1
                                        else
                                          (let uu____22435 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22435
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22436;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22437;_},uu____22438)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22455;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22456;_},uu____22457)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22474 -> tm1
                                           else
                                             (let uu____22484 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22484 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22504 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22514;
                         FStar_Syntax_Syntax.vars = uu____22515;_},args)
                      ->
                      let uu____22537 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22537
                      then
                        let uu____22538 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22538 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22583)::
                             (uu____22584,(arg,uu____22586))::[] ->
                             maybe_auto_squash arg
                         | (uu____22635,(arg,uu____22637))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22638)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22687)::uu____22688::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22739::(FStar_Pervasives_Native.Some (false
                                         ),uu____22740)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22791 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22805 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22805
                         then
                           let uu____22806 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22806 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22851)::uu____22852::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22903::(FStar_Pervasives_Native.Some (true
                                           ),uu____22904)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22955)::(uu____22956,(arg,uu____22958))::[]
                               -> maybe_auto_squash arg
                           | (uu____23007,(arg,uu____23009))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____23010)::[]
                               -> maybe_auto_squash arg
                           | uu____23059 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23073 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23073
                            then
                              let uu____23074 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23074 with
                              | uu____23119::(FStar_Pervasives_Native.Some
                                              (true ),uu____23120)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23171)::uu____23172::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23223)::(uu____23224,(arg,uu____23226))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23275,(p,uu____23277))::(uu____23278,
                                                                (q,uu____23280))::[]
                                  ->
                                  let uu____23327 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23327
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23329 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23343 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23343
                               then
                                 let uu____23344 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23344 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23389)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23390)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23441)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23442)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23493)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23494)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23545)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23546)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23597,(arg,uu____23599))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23600)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23649)::(uu____23650,(arg,uu____23652))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23701,(arg,uu____23703))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23704)::[]
                                     ->
                                     let uu____23753 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23753
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23754)::(uu____23755,(arg,uu____23757))::[]
                                     ->
                                     let uu____23806 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23806
                                 | (uu____23807,(p,uu____23809))::(uu____23810,
                                                                   (q,uu____23812))::[]
                                     ->
                                     let uu____23859 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23859
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23861 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23875 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23875
                                  then
                                    let uu____23876 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23876 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23921)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23952)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23983 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23997 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23997
                                     then
                                       match args with
                                       | (t,uu____23999)::[] ->
                                           let uu____24016 =
                                             let uu____24017 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24017.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24016 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24020::[],body,uu____24022)
                                                ->
                                                let uu____24049 = simp_t body
                                                   in
                                                (match uu____24049 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24052 -> tm1)
                                            | uu____24055 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24057))::(t,uu____24059)::[]
                                           ->
                                           let uu____24086 =
                                             let uu____24087 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24087.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24086 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24090::[],body,uu____24092)
                                                ->
                                                let uu____24119 = simp_t body
                                                   in
                                                (match uu____24119 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24122 -> tm1)
                                            | uu____24125 -> tm1)
                                       | uu____24126 -> tm1
                                     else
                                       (let uu____24136 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24136
                                        then
                                          match args with
                                          | (t,uu____24138)::[] ->
                                              let uu____24155 =
                                                let uu____24156 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24156.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24155 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24159::[],body,uu____24161)
                                                   ->
                                                   let uu____24188 =
                                                     simp_t body  in
                                                   (match uu____24188 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24191 -> tm1)
                                               | uu____24194 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24196))::(t,uu____24198)::[]
                                              ->
                                              let uu____24225 =
                                                let uu____24226 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24226.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24225 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24229::[],body,uu____24231)
                                                   ->
                                                   let uu____24258 =
                                                     simp_t body  in
                                                   (match uu____24258 with
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
                                                    | uu____24261 -> tm1)
                                               | uu____24264 -> tm1)
                                          | uu____24265 -> tm1
                                        else
                                          (let uu____24275 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24275
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24276;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24277;_},uu____24278)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24295;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24296;_},uu____24297)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24314 -> tm1
                                           else
                                             (let uu____24324 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24324 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24344 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24359 = simp_t t  in
                      (match uu____24359 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24362 ->
                      let uu____24385 = is_const_match tm1  in
                      (match uu____24385 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24388 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____24398  ->
               (let uu____24400 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24401 = FStar_Syntax_Print.term_to_string t  in
                let uu____24402 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24409 =
                  let uu____24410 =
                    let uu____24413 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24413
                     in
                  stack_to_string uu____24410  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24400 uu____24401 uu____24402 uu____24409);
               (let uu____24436 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24436
                then
                  let uu____24437 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24437 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24444 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24445 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24446 =
                          let uu____24447 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24447
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24444
                          uu____24445 uu____24446);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____24465 =
                     let uu____24466 =
                       let uu____24467 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____24467  in
                     FStar_Util.string_of_int uu____24466  in
                   let uu____24472 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____24473 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____24465 uu____24472 uu____24473)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____24479,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____24530  ->
                     let uu____24531 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____24531);
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
               let uu____24569 =
                 let uu___345_24570 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___345_24570.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___345_24570.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____24569
           | (Arg (Univ uu____24573,uu____24574,uu____24575))::uu____24576 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____24579,uu____24580))::uu____24581 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____24596,uu____24597),aq,r))::stack1
               when
               let uu____24647 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24647 ->
               let t2 =
                 let uu____24651 =
                   let uu____24656 =
                     let uu____24657 = closure_as_term cfg env_arg tm  in
                     (uu____24657, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____24656  in
                 uu____24651 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____24667),aq,r))::stack1 ->
               (log cfg
                  (fun uu____24720  ->
                     let uu____24721 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____24721);
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
                  (let uu____24733 = FStar_ST.op_Bang m  in
                   match uu____24733 with
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
                   | FStar_Pervasives_Native.Some (uu____24876,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____24929 =
                 log cfg
                   (fun uu____24933  ->
                      let uu____24934 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____24934);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____24940 =
                 let uu____24941 = FStar_Syntax_Subst.compress t1  in
                 uu____24941.FStar_Syntax_Syntax.n  in
               (match uu____24940 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____24968 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____24968  in
                    (log cfg
                       (fun uu____24972  ->
                          let uu____24973 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____24973);
                     (let uu____24974 = FStar_List.tl stack  in
                      norm cfg env1 uu____24974 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____24975);
                       FStar_Syntax_Syntax.pos = uu____24976;
                       FStar_Syntax_Syntax.vars = uu____24977;_},(e,uu____24979)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____25008 when
                    (cfg.steps).primops ->
                    let uu____25023 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____25023 with
                     | (hd1,args) ->
                         let uu____25060 =
                           let uu____25061 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____25061.FStar_Syntax_Syntax.n  in
                         (match uu____25060 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____25065 = find_prim_step cfg fv  in
                              (match uu____25065 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____25068; arity = uu____25069;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____25071;
                                     requires_binder_substitution =
                                       uu____25072;
                                     interpretation = uu____25073;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____25088 -> fallback " (3)" ())
                          | uu____25091 -> fallback " (4)" ()))
                | uu____25092 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____25115  ->
                     let uu____25116 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____25116);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____25125 =
                   log cfg1
                     (fun uu____25130  ->
                        let uu____25131 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____25132 =
                          let uu____25133 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____25160  ->
                                    match uu____25160 with
                                    | (p,uu____25170,uu____25171) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____25133
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____25131 uu____25132);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___253_25188  ->
                                match uu___253_25188 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____25189 -> false))
                         in
                      let steps =
                        let uu___346_25191 = cfg1.steps  in
                        {
                          beta = (uu___346_25191.beta);
                          iota = (uu___346_25191.iota);
                          zeta = false;
                          weak = (uu___346_25191.weak);
                          hnf = (uu___346_25191.hnf);
                          primops = (uu___346_25191.primops);
                          do_not_unfold_pure_lets =
                            (uu___346_25191.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___346_25191.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___346_25191.pure_subterms_within_computations);
                          simplify = (uu___346_25191.simplify);
                          erase_universes = (uu___346_25191.erase_universes);
                          allow_unbound_universes =
                            (uu___346_25191.allow_unbound_universes);
                          reify_ = (uu___346_25191.reify_);
                          compress_uvars = (uu___346_25191.compress_uvars);
                          no_full_norm = (uu___346_25191.no_full_norm);
                          check_no_uvars = (uu___346_25191.check_no_uvars);
                          unmeta = (uu___346_25191.unmeta);
                          unascribe = (uu___346_25191.unascribe);
                          in_full_norm_request =
                            (uu___346_25191.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___346_25191.weakly_reduce_scrutinee)
                        }  in
                      let uu___347_25196 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___347_25196.tcenv);
                        debug = (uu___347_25196.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___347_25196.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___347_25196.memoize_lazy);
                        normalize_pure_lets =
                          (uu___347_25196.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____25268 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____25297 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____25381  ->
                                    fun uu____25382  ->
                                      match (uu____25381, uu____25382) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____25521 = norm_pat env3 p1
                                             in
                                          (match uu____25521 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____25297 with
                           | (pats1,env3) ->
                               ((let uu___348_25683 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___348_25683.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___349_25702 = x  in
                            let uu____25703 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___349_25702.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___349_25702.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25703
                            }  in
                          ((let uu___350_25717 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___350_25717.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___351_25728 = x  in
                            let uu____25729 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___351_25728.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___351_25728.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25729
                            }  in
                          ((let uu___352_25743 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___352_25743.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___353_25759 = x  in
                            let uu____25760 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___353_25759.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___353_25759.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25760
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___354_25775 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___354_25775.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____25819 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____25849 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____25849 with
                                  | (p,wopt,e) ->
                                      let uu____25869 = norm_pat env1 p  in
                                      (match uu____25869 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____25924 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____25924
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____25941 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____25941
                      then
                        norm
                          (let uu___355_25946 = cfg1  in
                           {
                             steps =
                               (let uu___356_25949 = cfg1.steps  in
                                {
                                  beta = (uu___356_25949.beta);
                                  iota = (uu___356_25949.iota);
                                  zeta = (uu___356_25949.zeta);
                                  weak = (uu___356_25949.weak);
                                  hnf = (uu___356_25949.hnf);
                                  primops = (uu___356_25949.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___356_25949.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___356_25949.unfold_until);
                                  unfold_only = (uu___356_25949.unfold_only);
                                  unfold_fully =
                                    (uu___356_25949.unfold_fully);
                                  unfold_attr = (uu___356_25949.unfold_attr);
                                  unfold_tac = (uu___356_25949.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___356_25949.pure_subterms_within_computations);
                                  simplify = (uu___356_25949.simplify);
                                  erase_universes =
                                    (uu___356_25949.erase_universes);
                                  allow_unbound_universes =
                                    (uu___356_25949.allow_unbound_universes);
                                  reify_ = (uu___356_25949.reify_);
                                  compress_uvars =
                                    (uu___356_25949.compress_uvars);
                                  no_full_norm =
                                    (uu___356_25949.no_full_norm);
                                  check_no_uvars =
                                    (uu___356_25949.check_no_uvars);
                                  unmeta = (uu___356_25949.unmeta);
                                  unascribe = (uu___356_25949.unascribe);
                                  in_full_norm_request =
                                    (uu___356_25949.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___355_25946.tcenv);
                             debug = (uu___355_25946.debug);
                             delta_level = (uu___355_25946.delta_level);
                             primitive_steps =
                               (uu___355_25946.primitive_steps);
                             strong = (uu___355_25946.strong);
                             memoize_lazy = (uu___355_25946.memoize_lazy);
                             normalize_pure_lets =
                               (uu___355_25946.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____25951 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____25951)
                    in
                 let rec is_cons head1 =
                   let uu____25976 =
                     let uu____25977 = FStar_Syntax_Subst.compress head1  in
                     uu____25977.FStar_Syntax_Syntax.n  in
                   match uu____25976 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____25981) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____25986 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25987;
                         FStar_Syntax_Syntax.fv_delta = uu____25988;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25989;
                         FStar_Syntax_Syntax.fv_delta = uu____25990;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____25991);_}
                       -> true
                   | uu____25998 -> false  in
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
                   let uu____26161 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____26161 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____26248 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____26287 ->
                                 let uu____26288 =
                                   let uu____26289 = is_cons head1  in
                                   Prims.op_Negation uu____26289  in
                                 FStar_Util.Inr uu____26288)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____26314 =
                              let uu____26315 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____26315.FStar_Syntax_Syntax.n  in
                            (match uu____26314 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____26333 ->
                                 let uu____26334 =
                                   let uu____26335 = is_cons head1  in
                                   Prims.op_Negation uu____26335  in
                                 FStar_Util.Inr uu____26334))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____26412)::rest_a,(p1,uu____26415)::rest_p) ->
                       let uu____26459 = matches_pat t2 p1  in
                       (match uu____26459 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____26508 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____26626 = matches_pat scrutinee1 p1  in
                       (match uu____26626 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____26666  ->
                                  let uu____26667 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____26668 =
                                    let uu____26669 =
                                      FStar_List.map
                                        (fun uu____26679  ->
                                           match uu____26679 with
                                           | (uu____26684,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____26669
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____26667 uu____26668);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____26716  ->
                                       match uu____26716 with
                                       | (bv,t2) ->
                                           let uu____26739 =
                                             let uu____26746 =
                                               let uu____26749 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____26749
                                                in
                                             let uu____26750 =
                                               let uu____26751 =
                                                 let uu____26782 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____26782, false)
                                                  in
                                               Clos uu____26751  in
                                             (uu____26746, uu____26750)  in
                                           uu____26739 :: env2) env1 s
                                 in
                              let uu____26895 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____26895)))
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
    let uu____26922 =
      let uu____26925 = FStar_ST.op_Bang plugins  in p :: uu____26925  in
    FStar_ST.op_Colon_Equals plugins uu____26922  in
  let retrieve uu____27033 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____27110  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___254_27151  ->
                  match uu___254_27151 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____27155 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____27161 -> d  in
        let uu____27164 = to_fsteps s  in
        let uu____27165 =
          let uu____27166 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____27167 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____27168 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____27169 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____27170 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____27171 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____27172 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____27166;
            primop = uu____27167;
            unfolding = uu____27168;
            b380 = uu____27169;
            wpe = uu____27170;
            norm_delayed = uu____27171;
            print_normalized = uu____27172
          }  in
        let uu____27173 =
          let uu____27176 =
            let uu____27179 = retrieve_plugins ()  in
            FStar_List.append uu____27179 psteps  in
          add_steps built_in_primitive_steps uu____27176  in
        let uu____27182 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____27184 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____27184)
           in
        {
          steps = uu____27164;
          tcenv = e;
          debug = uu____27165;
          delta_level = d1;
          primitive_steps = uu____27173;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____27182
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
      fun t  -> let uu____27266 = config s e  in norm_comp uu____27266 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27283 = config [] env  in norm_universe uu____27283 [] u
  
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
        let uu____27307 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27307  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27314 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___357_27333 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___357_27333.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___357_27333.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27340 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27340
          then
            let ct1 =
              let uu____27342 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27342 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____27349 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27349
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___358_27353 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___358_27353.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___358_27353.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___358_27353.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___359_27355 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___359_27355.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___359_27355.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___359_27355.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___359_27355.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___360_27356 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___360_27356.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___360_27356.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27358 -> c
  
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
        let uu____27376 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27376  in
      let uu____27383 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____27383
      then
        let uu____27384 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____27384 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____27390  ->
                 let uu____27391 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____27391)
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
            ((let uu____27412 =
                let uu____27417 =
                  let uu____27418 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27418
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27417)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27412);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____27433 = config [AllowUnboundUniverses] env  in
          norm_comp uu____27433 [] c
        with
        | e ->
            ((let uu____27446 =
                let uu____27451 =
                  let uu____27452 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27452
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27451)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27446);
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
                   let uu____27497 =
                     let uu____27498 =
                       let uu____27505 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27505)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27498  in
                   mk uu____27497 t01.FStar_Syntax_Syntax.pos
               | uu____27510 -> t2)
          | uu____27511 -> t2  in
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
        let uu____27575 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27575 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27604 ->
                 let uu____27611 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27611 with
                  | (actuals,uu____27621,uu____27622) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27636 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27636 with
                         | (binders,args) ->
                             let uu____27647 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27647
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
      | uu____27661 ->
          let uu____27662 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27662 with
           | (head1,args) ->
               let uu____27699 =
                 let uu____27700 = FStar_Syntax_Subst.compress head1  in
                 uu____27700.FStar_Syntax_Syntax.n  in
               (match uu____27699 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27725 =
                      let uu____27738 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27738  in
                    (match uu____27725 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27768 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___365_27776 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___365_27776.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___365_27776.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___365_27776.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___365_27776.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___365_27776.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___365_27776.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___365_27776.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___365_27776.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___365_27776.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___365_27776.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___365_27776.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___365_27776.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___365_27776.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___365_27776.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___365_27776.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___365_27776.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___365_27776.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___365_27776.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___365_27776.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___365_27776.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___365_27776.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___365_27776.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___365_27776.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___365_27776.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___365_27776.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___365_27776.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___365_27776.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___365_27776.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___365_27776.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___365_27776.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___365_27776.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___365_27776.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___365_27776.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___365_27776.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___365_27776.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___365_27776.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____27768 with
                            | (uu____27777,ty,uu____27779) ->
                                eta_expand_with_type env t ty))
                | uu____27780 ->
                    let uu____27781 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___366_27789 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___366_27789.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___366_27789.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___366_27789.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___366_27789.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___366_27789.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___366_27789.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___366_27789.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___366_27789.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___366_27789.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___366_27789.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___366_27789.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___366_27789.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___366_27789.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___366_27789.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___366_27789.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___366_27789.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___366_27789.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___366_27789.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___366_27789.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___366_27789.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___366_27789.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___366_27789.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___366_27789.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___366_27789.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___366_27789.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___366_27789.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___366_27789.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___366_27789.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___366_27789.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___366_27789.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___366_27789.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___366_27789.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___366_27789.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___366_27789.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___366_27789.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___366_27789.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____27781 with
                     | (uu____27790,ty,uu____27792) ->
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
      let uu___367_27865 = x  in
      let uu____27866 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___367_27865.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___367_27865.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27866
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27869 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27894 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27895 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27896 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27897 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27904 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27905 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27906 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___368_27936 = rc  in
          let uu____27937 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27946 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___368_27936.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27937;
            FStar_Syntax_Syntax.residual_flags = uu____27946
          }  in
        let uu____27949 =
          let uu____27950 =
            let uu____27967 = elim_delayed_subst_binders bs  in
            let uu____27974 = elim_delayed_subst_term t2  in
            let uu____27977 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27967, uu____27974, uu____27977)  in
          FStar_Syntax_Syntax.Tm_abs uu____27950  in
        mk1 uu____27949
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28008 =
          let uu____28009 =
            let uu____28022 = elim_delayed_subst_binders bs  in
            let uu____28029 = elim_delayed_subst_comp c  in
            (uu____28022, uu____28029)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28009  in
        mk1 uu____28008
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28046 =
          let uu____28047 =
            let uu____28054 = elim_bv bv  in
            let uu____28055 = elim_delayed_subst_term phi  in
            (uu____28054, uu____28055)  in
          FStar_Syntax_Syntax.Tm_refine uu____28047  in
        mk1 uu____28046
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28082 =
          let uu____28083 =
            let uu____28098 = elim_delayed_subst_term t2  in
            let uu____28101 = elim_delayed_subst_args args  in
            (uu____28098, uu____28101)  in
          FStar_Syntax_Syntax.Tm_app uu____28083  in
        mk1 uu____28082
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___369_28169 = p  in
              let uu____28170 =
                let uu____28171 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28171  in
              {
                FStar_Syntax_Syntax.v = uu____28170;
                FStar_Syntax_Syntax.p =
                  (uu___369_28169.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___370_28173 = p  in
              let uu____28174 =
                let uu____28175 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28175  in
              {
                FStar_Syntax_Syntax.v = uu____28174;
                FStar_Syntax_Syntax.p =
                  (uu___370_28173.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___371_28182 = p  in
              let uu____28183 =
                let uu____28184 =
                  let uu____28191 = elim_bv x  in
                  let uu____28192 = elim_delayed_subst_term t0  in
                  (uu____28191, uu____28192)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28184  in
              {
                FStar_Syntax_Syntax.v = uu____28183;
                FStar_Syntax_Syntax.p =
                  (uu___371_28182.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___372_28215 = p  in
              let uu____28216 =
                let uu____28217 =
                  let uu____28230 =
                    FStar_List.map
                      (fun uu____28253  ->
                         match uu____28253 with
                         | (x,b) ->
                             let uu____28266 = elim_pat x  in
                             (uu____28266, b)) pats
                     in
                  (fv, uu____28230)  in
                FStar_Syntax_Syntax.Pat_cons uu____28217  in
              {
                FStar_Syntax_Syntax.v = uu____28216;
                FStar_Syntax_Syntax.p =
                  (uu___372_28215.FStar_Syntax_Syntax.p)
              }
          | uu____28279 -> p  in
        let elim_branch uu____28303 =
          match uu____28303 with
          | (pat,wopt,t3) ->
              let uu____28329 = elim_pat pat  in
              let uu____28332 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28335 = elim_delayed_subst_term t3  in
              (uu____28329, uu____28332, uu____28335)
           in
        let uu____28340 =
          let uu____28341 =
            let uu____28364 = elim_delayed_subst_term t2  in
            let uu____28367 = FStar_List.map elim_branch branches  in
            (uu____28364, uu____28367)  in
          FStar_Syntax_Syntax.Tm_match uu____28341  in
        mk1 uu____28340
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28498 =
          match uu____28498 with
          | (tc,topt) ->
              let uu____28533 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28543 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28543
                | FStar_Util.Inr c ->
                    let uu____28545 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28545
                 in
              let uu____28546 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28533, uu____28546)
           in
        let uu____28555 =
          let uu____28556 =
            let uu____28583 = elim_delayed_subst_term t2  in
            let uu____28586 = elim_ascription a  in
            (uu____28583, uu____28586, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28556  in
        mk1 uu____28555
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___373_28647 = lb  in
          let uu____28648 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28651 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___373_28647.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___373_28647.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28648;
            FStar_Syntax_Syntax.lbeff =
              (uu___373_28647.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28651;
            FStar_Syntax_Syntax.lbattrs =
              (uu___373_28647.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___373_28647.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28654 =
          let uu____28655 =
            let uu____28668 =
              let uu____28675 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28675)  in
            let uu____28684 = elim_delayed_subst_term t2  in
            (uu____28668, uu____28684)  in
          FStar_Syntax_Syntax.Tm_let uu____28655  in
        mk1 uu____28654
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28734 =
          let uu____28735 =
            let uu____28742 = elim_delayed_subst_term tm  in
            (uu____28742, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28735  in
        mk1 uu____28734
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28753 =
          let uu____28754 =
            let uu____28761 = elim_delayed_subst_term t2  in
            let uu____28764 = elim_delayed_subst_meta md  in
            (uu____28761, uu____28764)  in
          FStar_Syntax_Syntax.Tm_meta uu____28754  in
        mk1 uu____28753

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___255_28773  ->
         match uu___255_28773 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28777 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28777
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
        let uu____28800 =
          let uu____28801 =
            let uu____28810 = elim_delayed_subst_term t  in
            (uu____28810, uopt)  in
          FStar_Syntax_Syntax.Total uu____28801  in
        mk1 uu____28800
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28827 =
          let uu____28828 =
            let uu____28837 = elim_delayed_subst_term t  in
            (uu____28837, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28828  in
        mk1 uu____28827
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___374_28846 = ct  in
          let uu____28847 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28850 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28859 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___374_28846.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___374_28846.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28847;
            FStar_Syntax_Syntax.effect_args = uu____28850;
            FStar_Syntax_Syntax.flags = uu____28859
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___256_28862  ->
    match uu___256_28862 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____28874 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____28874
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28907 =
          let uu____28914 = elim_delayed_subst_term t  in (m, uu____28914)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28907
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28926 =
          let uu____28935 = elim_delayed_subst_term t  in
          (m1, m2, uu____28935)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28926
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____28962  ->
         match uu____28962 with
         | (t,q) ->
             let uu____28973 = elim_delayed_subst_term t  in (uu____28973, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28993  ->
         match uu____28993 with
         | (x,q) ->
             let uu____29004 =
               let uu___375_29005 = x  in
               let uu____29006 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___375_29005.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___375_29005.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29006
               }  in
             (uu____29004, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term'
                                                          FStar_Syntax_Syntax.syntax,
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
            | (uu____29098,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29124,FStar_Util.Inl t) ->
                let uu____29142 =
                  let uu____29149 =
                    let uu____29150 =
                      let uu____29163 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29163)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29150  in
                  FStar_Syntax_Syntax.mk uu____29149  in
                uu____29142 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29177 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29177 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29207 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29270 ->
                    let uu____29271 =
                      let uu____29280 =
                        let uu____29281 = FStar_Syntax_Subst.compress t4  in
                        uu____29281.FStar_Syntax_Syntax.n  in
                      (uu____29280, tc)  in
                    (match uu____29271 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29308) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29349) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29388,FStar_Util.Inl uu____29389) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29416 -> failwith "Impossible")
                 in
              (match uu____29207 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____29541 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29541 with
          | (univ_names1,binders1,tc) ->
              let uu____29607 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29607)
  
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
          let uu____29656 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29656 with
          | (univ_names1,binders1,tc) ->
              let uu____29722 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29722)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29761 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29761 with
           | (univ_names1,binders1,typ1) ->
               let uu___376_29795 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___376_29795.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___376_29795.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___376_29795.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___376_29795.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___377_29810 = s  in
          let uu____29811 =
            let uu____29812 =
              let uu____29821 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29821, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29812  in
          {
            FStar_Syntax_Syntax.sigel = uu____29811;
            FStar_Syntax_Syntax.sigrng =
              (uu___377_29810.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___377_29810.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___377_29810.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___377_29810.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29838 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29838 with
           | (univ_names1,uu____29858,typ1) ->
               let uu___378_29876 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___378_29876.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___378_29876.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___378_29876.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___378_29876.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29882 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29882 with
           | (univ_names1,uu____29902,typ1) ->
               let uu___379_29920 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_29920.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_29920.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_29920.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_29920.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29948 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29948 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29973 =
                            let uu____29974 =
                              let uu____29975 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29975  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29974
                             in
                          elim_delayed_subst_term uu____29973  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___380_29978 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___380_29978.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___380_29978.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___380_29978.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___380_29978.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___381_29979 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___381_29979.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_29979.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_29979.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_29979.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___382_29985 = s  in
          let uu____29986 =
            let uu____29987 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29987  in
          {
            FStar_Syntax_Syntax.sigel = uu____29986;
            FStar_Syntax_Syntax.sigrng =
              (uu___382_29985.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_29985.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_29985.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_29985.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29991 = elim_uvars_aux_t env us [] t  in
          (match uu____29991 with
           | (us1,uu____30011,t1) ->
               let uu___383_30029 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_30029.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_30029.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_30029.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_30029.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____30030 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30032 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____30032 with
           | (univs1,binders,signature) ->
               let uu____30066 =
                 let uu____30071 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30071 with
                 | (univs_opening,univs2) ->
                     let uu____30094 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30094)
                  in
               (match uu____30066 with
                | (univs_opening,univs_closing) ->
                    let uu____30097 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30103 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30104 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30103, uu____30104)  in
                    (match uu____30097 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30128 =
                           match uu____30128 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30146 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30146 with
                                | (us1,t1) ->
                                    let uu____30157 =
                                      let uu____30166 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30177 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30166, uu____30177)  in
                                    (match uu____30157 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30206 =
                                           let uu____30215 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____30226 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____30215, uu____30226)  in
                                         (match uu____30206 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30256 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30256
                                                 in
                                              let uu____30257 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30257 with
                                               | (uu____30280,uu____30281,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30300 =
                                                       let uu____30301 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30301
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30300
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30310 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30310 with
                           | (uu____30327,uu____30328,t1) -> t1  in
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
                             | uu____30398 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30423 =
                               let uu____30424 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30424.FStar_Syntax_Syntax.n  in
                             match uu____30423 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30483 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30514 =
                               let uu____30515 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30515.FStar_Syntax_Syntax.n  in
                             match uu____30514 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30536) ->
                                 let uu____30557 = destruct_action_body body
                                    in
                                 (match uu____30557 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30602 ->
                                 let uu____30603 = destruct_action_body t  in
                                 (match uu____30603 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30652 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30652 with
                           | (action_univs,t) ->
                               let uu____30661 = destruct_action_typ_templ t
                                  in
                               (match uu____30661 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___384_30702 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___384_30702.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___384_30702.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___385_30704 = ed  in
                           let uu____30705 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30706 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30707 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30708 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30709 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30710 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30711 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____30712 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____30713 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____30714 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30715 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____30716 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30717 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30718 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___385_30704.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___385_30704.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____30705;
                             FStar_Syntax_Syntax.bind_wp = uu____30706;
                             FStar_Syntax_Syntax.if_then_else = uu____30707;
                             FStar_Syntax_Syntax.ite_wp = uu____30708;
                             FStar_Syntax_Syntax.stronger = uu____30709;
                             FStar_Syntax_Syntax.close_wp = uu____30710;
                             FStar_Syntax_Syntax.assert_p = uu____30711;
                             FStar_Syntax_Syntax.assume_p = uu____30712;
                             FStar_Syntax_Syntax.null_wp = uu____30713;
                             FStar_Syntax_Syntax.trivial = uu____30714;
                             FStar_Syntax_Syntax.repr = uu____30715;
                             FStar_Syntax_Syntax.return_repr = uu____30716;
                             FStar_Syntax_Syntax.bind_repr = uu____30717;
                             FStar_Syntax_Syntax.actions = uu____30718;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___385_30704.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___386_30721 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___386_30721.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___386_30721.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___386_30721.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___386_30721.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___257_30742 =
            match uu___257_30742 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30773 = elim_uvars_aux_t env us [] t  in
                (match uu____30773 with
                 | (us1,uu____30801,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___387_30828 = sub_eff  in
            let uu____30829 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30832 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___387_30828.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___387_30828.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30829;
              FStar_Syntax_Syntax.lift = uu____30832
            }  in
          let uu___388_30835 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___388_30835.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___388_30835.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___388_30835.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___388_30835.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____30845 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30845 with
           | (univ_names1,binders1,comp1) ->
               let uu___389_30879 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___389_30879.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___389_30879.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___389_30879.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___389_30879.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30882 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30883 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  