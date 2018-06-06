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
                 let uu____3662 =
                   let uu____3663 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3663  in
                 match uu____3662 with
                 | Univ u3 ->
                     ((let uu____3682 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug cfg.tcenv)
                           (FStar_Options.Other "univ_norm")
                          in
                       if uu____3682
                       then
                         let uu____3683 =
                           FStar_Syntax_Print.univ_to_string u3  in
                         FStar_Util.print1 "Univ (in norm_universe): %s\n"
                           uu____3683
                       else ());
                      aux u3)
                 | Dummy  -> [u2]
                 | uu____3685 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3693 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3699 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3708 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3717 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3724 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3724 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3741 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3741 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3749 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3757 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3757 with
                                  | (uu____3762,m) -> n1 <= m))
                           in
                        if uu____3749 then rest1 else us1
                    | uu____3767 -> us1)
               | uu____3772 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3776 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3776
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3780 = aux u  in
           match uu____3780 with
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
            (fun uu____3928  ->
               let uu____3929 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3930 = env_to_string env  in
               let uu____3931 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3929 uu____3930 uu____3931);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3940 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3943 ->
                    let uu____3966 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3966
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3967 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3968 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3969 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3970 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3994 ->
                           let uu____4007 =
                             let uu____4008 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4009 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4008 uu____4009
                              in
                           failwith uu____4007
                       | uu____4012 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___243_4047  ->
                                         match uu___243_4047 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4054 =
                                               let uu____4061 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4061)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4054
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___287_4071 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___287_4071.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___287_4071.FStar_Syntax_Syntax.sort)
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
                                              | uu____4076 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4079 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___288_4083 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___288_4083.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___288_4083.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4104 =
                        let uu____4105 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4105  in
                      mk uu____4104 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4113 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4113  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4115 = lookup_bvar env x  in
                    (match uu____4115 with
                     | Univ uu____4118 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___289_4122 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___289_4122.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___289_4122.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4128,uu____4129) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4214  ->
                              fun stack1  ->
                                match uu____4214 with
                                | (a,aq) ->
                                    let uu____4226 =
                                      let uu____4227 =
                                        let uu____4234 =
                                          let uu____4235 =
                                            let uu____4266 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4266, false)  in
                                          Clos uu____4235  in
                                        (uu____4234, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4227  in
                                    uu____4226 :: stack1) args)
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
                    let uu____4442 = close_binders cfg env bs  in
                    (match uu____4442 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4489 =
                      let uu____4500 =
                        let uu____4507 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4507]  in
                      close_binders cfg env uu____4500  in
                    (match uu____4489 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4542 =
                             let uu____4543 =
                               let uu____4550 =
                                 let uu____4551 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4551
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4550, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4543  in
                           mk uu____4542 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4642 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4642
                      | FStar_Util.Inr c ->
                          let uu____4656 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4656
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4675 =
                        let uu____4676 =
                          let uu____4703 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4703, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4676  in
                      mk uu____4675 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4749 =
                            let uu____4750 =
                              let uu____4757 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4757, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4750  in
                          mk uu____4749 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4809  -> dummy :: env1) env
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
                    let uu____4830 =
                      let uu____4841 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4841
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4860 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___290_4876 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___290_4876.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___290_4876.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4860))
                       in
                    (match uu____4830 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___291_4894 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___291_4894.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___291_4894.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___291_4894.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___291_4894.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4908,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4971  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4988 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4988
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5000  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5024 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5024
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___292_5032 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___292_5032.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___292_5032.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___293_5033 = lb  in
                      let uu____5034 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___293_5033.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___293_5033.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5034;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___293_5033.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___293_5033.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5066  -> fun env1  -> dummy :: env1)
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
            (fun uu____5155  ->
               let uu____5156 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5157 = env_to_string env  in
               let uu____5158 = stack_to_string stack  in
               let uu____5159 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5156 uu____5157 uu____5158 uu____5159);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5164,uu____5165),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5242 = close_binders cfg env' bs  in
               (match uu____5242 with
                | (bs1,uu____5256) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5272 =
                      let uu___294_5275 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___294_5275.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___294_5275.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5272)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5331 =
                 match uu____5331 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5446 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5475 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5559  ->
                                     fun uu____5560  ->
                                       match (uu____5559, uu____5560) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5699 = norm_pat env4 p1
                                              in
                                           (match uu____5699 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5475 with
                            | (pats1,env4) ->
                                ((let uu___295_5861 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___295_5861.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___296_5880 = x  in
                             let uu____5881 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___296_5880.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___296_5880.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5881
                             }  in
                           ((let uu___297_5895 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___297_5895.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___298_5906 = x  in
                             let uu____5907 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___298_5906.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___298_5906.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5907
                             }  in
                           ((let uu___299_5921 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___299_5921.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___300_5937 = x  in
                             let uu____5938 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___300_5937.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___300_5937.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5938
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___301_5955 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___301_5955.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5960 = norm_pat env2 pat  in
                     (match uu____5960 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6029 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6029
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6048 =
                   let uu____6049 =
                     let uu____6072 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6072)  in
                   FStar_Syntax_Syntax.Tm_match uu____6049  in
                 mk uu____6048 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6185 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6274  ->
                                       match uu____6274 with
                                       | (a,q) ->
                                           let uu____6293 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6293, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6185
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6304 =
                       let uu____6311 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6311)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6304
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6323 =
                       let uu____6332 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6332)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6323
                 | uu____6337 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6343 -> failwith "Impossible: unexpected stack element")

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
        let uu____6357 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6430  ->
                  fun uu____6431  ->
                    match (uu____6430, uu____6431) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___302_6549 = b  in
                          let uu____6550 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___302_6549.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___302_6549.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6550
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6357 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6667 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6680 = inline_closure_env cfg env [] t  in
                 let uu____6681 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6680 uu____6681
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6694 = inline_closure_env cfg env [] t  in
                 let uu____6695 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6694 uu____6695
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6739  ->
                           match uu____6739 with
                           | (a,q) ->
                               let uu____6752 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6752, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___244_6767  ->
                           match uu___244_6767 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6771 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6771
                           | f -> f))
                    in
                 let uu____6775 =
                   let uu___303_6776 = c1  in
                   let uu____6777 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6777;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___303_6776.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6775)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___245_6787  ->
            match uu___245_6787 with
            | FStar_Syntax_Syntax.DECREASES uu____6788 -> false
            | uu____6791 -> true))

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
                   (fun uu___246_6809  ->
                      match uu___246_6809 with
                      | FStar_Syntax_Syntax.DECREASES uu____6810 -> false
                      | uu____6813 -> true))
               in
            let rc1 =
              let uu___304_6815 = rc  in
              let uu____6816 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___304_6815.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6816;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6825 -> lopt

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
    let uu____6930 =
      let uu____6939 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6939  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6930  in
  let arg_as_bounded_int uu____6965 =
    match uu____6965 with
    | (a,uu____6977) ->
        let uu____6984 =
          let uu____6985 = FStar_Syntax_Subst.compress a  in
          uu____6985.FStar_Syntax_Syntax.n  in
        (match uu____6984 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6995;
                FStar_Syntax_Syntax.vars = uu____6996;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6998;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6999;_},uu____7000)::[])
             when
             let uu____7039 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7039 "int_to_t" ->
             let uu____7040 =
               let uu____7045 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7045)  in
             FStar_Pervasives_Native.Some uu____7040
         | uu____7050 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7098 = f a  in FStar_Pervasives_Native.Some uu____7098
    | uu____7099 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7155 = f a0 a1  in FStar_Pervasives_Native.Some uu____7155
    | uu____7156 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7214 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7214  in
  let binary_op as_a f res args =
    let uu____7285 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7285  in
  let as_primitive_step is_strong uu____7322 =
    match uu____7322 with
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
           let uu____7382 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7382)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7418 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7418)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7447 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7447)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7483 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7483)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7519 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7519)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7651 =
          let uu____7660 = as_a a  in
          let uu____7663 = as_b b  in (uu____7660, uu____7663)  in
        (match uu____7651 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7678 =
               let uu____7679 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7679  in
             FStar_Pervasives_Native.Some uu____7678
         | uu____7680 -> FStar_Pervasives_Native.None)
    | uu____7689 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7709 =
        let uu____7710 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7710  in
      mk uu____7709 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7724 =
      let uu____7727 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7727  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7724  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7769 =
      let uu____7770 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7770  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7769
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7834 = arg_as_string a1  in
        (match uu____7834 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7840 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7840 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7853 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7853
              | uu____7854 -> FStar_Pervasives_Native.None)
         | uu____7859 -> FStar_Pervasives_Native.None)
    | uu____7862 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7882 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7882
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7919 =
          let uu____7940 = arg_as_string fn  in
          let uu____7943 = arg_as_int from_line  in
          let uu____7946 = arg_as_int from_col  in
          let uu____7949 = arg_as_int to_line  in
          let uu____7952 = arg_as_int to_col  in
          (uu____7940, uu____7943, uu____7946, uu____7949, uu____7952)  in
        (match uu____7919 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7983 =
                 let uu____7984 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7985 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7984 uu____7985  in
               let uu____7986 =
                 let uu____7987 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7988 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7987 uu____7988  in
               FStar_Range.mk_range fn1 uu____7983 uu____7986  in
             let uu____7989 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7989
         | uu____7990 -> FStar_Pervasives_Native.None)
    | uu____8011 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8044)::(a1,uu____8046)::(a2,uu____8048)::[] ->
        let uu____8085 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8085 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8090 -> FStar_Pervasives_Native.None)
    | uu____8091 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8122)::[] ->
        let uu____8131 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8131 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8137 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8137
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8138 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8164 =
      let uu____8181 =
        let uu____8198 =
          let uu____8215 =
            let uu____8232 =
              let uu____8249 =
                let uu____8266 =
                  let uu____8283 =
                    let uu____8300 =
                      let uu____8317 =
                        let uu____8334 =
                          let uu____8351 =
                            let uu____8368 =
                              let uu____8385 =
                                let uu____8402 =
                                  let uu____8419 =
                                    let uu____8436 =
                                      let uu____8453 =
                                        let uu____8470 =
                                          let uu____8487 =
                                            let uu____8504 =
                                              let uu____8521 =
                                                let uu____8536 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8536,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8545 =
                                                let uu____8562 =
                                                  let uu____8577 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8577,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8590 =
                                                  let uu____8607 =
                                                    let uu____8622 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8622,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8631 =
                                                    let uu____8648 =
                                                      let uu____8663 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8663,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8648]  in
                                                  uu____8607 :: uu____8631
                                                   in
                                                uu____8562 :: uu____8590  in
                                              uu____8521 :: uu____8545  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8504
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8487
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8470
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8453
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8436
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8883 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8883 y)))
                                    :: uu____8419
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8402
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8385
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8368
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8351
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8334
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8317
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9078 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9078)))
                      :: uu____8300
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9108 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9108)))
                    :: uu____8283
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9138 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9138)))
                  :: uu____8266
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9168 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9168)))
                :: uu____8249
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8232
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8215
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8198
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8181
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8164
     in
  let weak_ops =
    let uu____9323 =
      let uu____9338 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9338, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9323]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9418 =
        let uu____9423 =
          let uu____9424 = FStar_Syntax_Syntax.as_arg c  in [uu____9424]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9423  in
      uu____9418 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9498 =
                let uu____9513 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9513, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9535  ->
                          fun uu____9536  ->
                            match (uu____9535, uu____9536) with
                            | ((int_to_t1,x),(uu____9555,y)) ->
                                let uu____9565 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9565)))
                 in
              let uu____9566 =
                let uu____9583 =
                  let uu____9598 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9598, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9620  ->
                            fun uu____9621  ->
                              match (uu____9620, uu____9621) with
                              | ((int_to_t1,x),(uu____9640,y)) ->
                                  let uu____9650 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9650)))
                   in
                let uu____9651 =
                  let uu____9668 =
                    let uu____9683 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9683, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9705  ->
                              fun uu____9706  ->
                                match (uu____9705, uu____9706) with
                                | ((int_to_t1,x),(uu____9725,y)) ->
                                    let uu____9735 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9735)))
                     in
                  let uu____9736 =
                    let uu____9753 =
                      let uu____9768 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9768, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9786  ->
                                match uu____9786 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9753]  in
                  uu____9668 :: uu____9736  in
                uu____9583 :: uu____9651  in
              uu____9498 :: uu____9566))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9916 =
                let uu____9931 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9931, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9953  ->
                          fun uu____9954  ->
                            match (uu____9953, uu____9954) with
                            | ((int_to_t1,x),(uu____9973,y)) ->
                                let uu____9983 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9983)))
                 in
              let uu____9984 =
                let uu____10001 =
                  let uu____10016 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10016, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10038  ->
                            fun uu____10039  ->
                              match (uu____10038, uu____10039) with
                              | ((int_to_t1,x),(uu____10058,y)) ->
                                  let uu____10068 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10068)))
                   in
                [uu____10001]  in
              uu____9916 :: uu____9984))
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
    | (_typ,uu____10198)::(a1,uu____10200)::(a2,uu____10202)::[] ->
        let uu____10239 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10239 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___305_10243 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___305_10243.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___305_10243.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10245 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10245.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10245.FStar_Syntax_Syntax.vars)
                })
         | uu____10246 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10248)::uu____10249::(a1,uu____10251)::(a2,uu____10253)::[]
        ->
        let uu____10302 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10302 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___305_10306 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___305_10306.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___305_10306.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10308 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10308.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10308.FStar_Syntax_Syntax.vars)
                })
         | uu____10309 -> FStar_Pervasives_Native.None)
    | uu____10310 -> failwith "Unexpected number of arguments"  in
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
    let uu____10364 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10364 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10416 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10416) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10478  ->
           fun subst1  ->
             match uu____10478 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10519,uu____10520)) ->
                      let uu____10579 = b  in
                      (match uu____10579 with
                       | (bv,uu____10587) ->
                           let uu____10588 =
                             let uu____10589 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10589  in
                           if uu____10588
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10594 = unembed_binder term1  in
                              match uu____10594 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10601 =
                                      let uu___307_10602 = bv  in
                                      let uu____10603 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___307_10602.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___307_10602.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10603
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10601
                                     in
                                  let b_for_x =
                                    let uu____10607 =
                                      let uu____10614 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10614)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10607  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___247_10628  ->
                                         match uu___247_10628 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10629,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10631;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10632;_})
                                             ->
                                             let uu____10637 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10637
                                         | uu____10638 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10639 -> subst1)) env []
  
let reduce_primops :
  'Auu____10662 'Auu____10663 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10662) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10663 ->
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
            (let uu____10711 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10711 with
             | (head1,args) ->
                 let uu____10750 =
                   let uu____10751 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10751.FStar_Syntax_Syntax.n  in
                 (match uu____10750 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10757 = find_prim_step cfg fv  in
                      (match uu____10757 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10783  ->
                                   let uu____10784 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10785 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10792 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10784 uu____10785 uu____10792);
                              tm)
                           else
                             (let uu____10794 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10794 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10907  ->
                                        let uu____10908 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10908);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10911  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10913 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10913 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10921  ->
                                              let uu____10922 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10922);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10928  ->
                                              let uu____10929 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10930 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10929 uu____10930);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10931 ->
                           (log_primops cfg
                              (fun uu____10935  ->
                                 let uu____10936 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10936);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10940  ->
                            let uu____10941 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10941);
                       (match args with
                        | (a1,uu____10945)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10962 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10974  ->
                            let uu____10975 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10975);
                       (match args with
                        | (t,uu____10979)::(r,uu____10981)::[] ->
                            let uu____11008 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11008 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11014 -> tm))
                  | uu____11023 -> tm))
  
let reduce_equality :
  'Auu____11034 'Auu____11035 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11034) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11035 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___308_11081 = cfg  in
         {
           steps =
             (let uu___309_11084 = default_steps  in
              {
                beta = (uu___309_11084.beta);
                iota = (uu___309_11084.iota);
                zeta = (uu___309_11084.zeta);
                weak = (uu___309_11084.weak);
                hnf = (uu___309_11084.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___309_11084.do_not_unfold_pure_lets);
                unfold_until = (uu___309_11084.unfold_until);
                unfold_only = (uu___309_11084.unfold_only);
                unfold_fully = (uu___309_11084.unfold_fully);
                unfold_attr = (uu___309_11084.unfold_attr);
                unfold_tac = (uu___309_11084.unfold_tac);
                pure_subterms_within_computations =
                  (uu___309_11084.pure_subterms_within_computations);
                simplify = (uu___309_11084.simplify);
                erase_universes = (uu___309_11084.erase_universes);
                allow_unbound_universes =
                  (uu___309_11084.allow_unbound_universes);
                reify_ = (uu___309_11084.reify_);
                compress_uvars = (uu___309_11084.compress_uvars);
                no_full_norm = (uu___309_11084.no_full_norm);
                check_no_uvars = (uu___309_11084.check_no_uvars);
                unmeta = (uu___309_11084.unmeta);
                unascribe = (uu___309_11084.unascribe);
                in_full_norm_request = (uu___309_11084.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___309_11084.weakly_reduce_scrutinee)
              });
           tcenv = (uu___308_11081.tcenv);
           debug = (uu___308_11081.debug);
           delta_level = (uu___308_11081.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___308_11081.strong);
           memoize_lazy = (uu___308_11081.memoize_lazy);
           normalize_pure_lets = (uu___308_11081.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11091 .
    FStar_Syntax_Syntax.term -> 'Auu____11091 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11106 =
        let uu____11113 =
          let uu____11114 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11114.FStar_Syntax_Syntax.n  in
        (uu____11113, args)  in
      match uu____11106 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11120::uu____11121::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11125::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11130::uu____11131::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11134 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___248_11147  ->
    match uu___248_11147 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11153 =
          let uu____11156 =
            let uu____11157 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11157  in
          [uu____11156]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11153
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11163 =
          let uu____11166 =
            let uu____11167 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11167  in
          [uu____11166]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11163
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11190 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11190)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11241 =
            let uu____11246 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11246 s  in
          match uu____11241 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11262 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11262
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11288::(tm,uu____11290)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11319)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11340)::uu____11341::(tm,uu____11343)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11384 =
              let uu____11389 = full_norm steps  in parse_steps uu____11389
               in
            (match uu____11384 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11428 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___249_11447  ->
    match uu___249_11447 with
    | (App
        (uu____11450,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11451;
                       FStar_Syntax_Syntax.vars = uu____11452;_},uu____11453,uu____11454))::uu____11455
        -> true
    | uu____11460 -> false
  
let firstn :
  'Auu____11469 .
    Prims.int ->
      'Auu____11469 Prims.list ->
        ('Auu____11469 Prims.list,'Auu____11469 Prims.list)
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
          (uu____11511,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11512;
                         FStar_Syntax_Syntax.vars = uu____11513;_},uu____11514,uu____11515))::uu____11516
          -> (cfg.steps).reify_
      | uu____11521 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11544) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11554) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11573  ->
                  match uu____11573 with
                  | (a,uu____11581) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11587 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11610 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11611 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11624 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11625 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11626 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11627 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11628 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11629 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11636 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11643 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11656 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11673 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11686 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11693 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11755  ->
                   match uu____11755 with
                   | (a,uu____11763) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11770) ->
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
                     (fun uu____11892  ->
                        match uu____11892 with
                        | (a,uu____11900) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11905,uu____11906,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11912,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11918 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11925 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11926 -> false))
  
let decide_unfolding :
  'Auu____11941 .
    cfg ->
      'Auu____11941 Prims.list ->
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
              log_unfolding cfg
                (fun uu____12033  ->
                   let uu____12034 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____12035 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____12036 =
                     let uu____12037 =
                       let uu____12040 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____12040
                        in
                     stack_to_string uu____12037  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____12034 uu____12035 uu____12036);
              (let attrs =
                 let uu____12066 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____12066 with
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
                   (fun uu____12194  ->
                      fun uu____12195  ->
                        match (uu____12194, uu____12195) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____12255 =
                 match uu____12255 with
                 | (x,y,z) ->
                     let uu____12265 = FStar_Util.string_of_bool x  in
                     let uu____12266 = FStar_Util.string_of_bool y  in
                     let uu____12267 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____12265 uu____12266
                       uu____12267
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____12313 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____12359  ->
                           let uu____12360 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____12361 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____12360 uu____12361);
                      if b then reif else no)
                 | uu____12369 when
                     let uu____12410 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____12410 -> no
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____12414),uu____12415);
                        FStar_Syntax_Syntax.sigrng = uu____12416;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____12418;
                        FStar_Syntax_Syntax.sigattrs = uu____12419;_},uu____12420),uu____12421),uu____12422,uu____12423,uu____12424)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     -> no
                 | (uu____12527,uu____12528,uu____12529,uu____12530) when
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
                          ((is_rec,uu____12596),uu____12597);
                        FStar_Syntax_Syntax.sigrng = uu____12598;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____12600;
                        FStar_Syntax_Syntax.sigattrs = uu____12601;_},uu____12602),uu____12603),uu____12604,uu____12605,uu____12606)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     no
                 | (uu____12709,FStar_Pervasives_Native.Some
                    uu____12710,uu____12711,uu____12712) ->
                     (log_unfolding cfg
                        (fun uu____12780  ->
                           let uu____12781 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____12781);
                      (let uu____12782 =
                         let uu____12791 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____12811 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____12811
                            in
                         let uu____12818 =
                           let uu____12827 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____12847 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____12847
                              in
                           let uu____12856 =
                             let uu____12865 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____12885 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____12885
                                in
                             [uu____12865]  in
                           uu____12827 :: uu____12856  in
                         uu____12791 :: uu____12818  in
                       comb_or uu____12782))
                 | (uu____12916,uu____12917,FStar_Pervasives_Native.Some
                    uu____12918,uu____12919) ->
                     (log_unfolding cfg
                        (fun uu____12987  ->
                           let uu____12988 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____12988);
                      (let uu____12989 =
                         let uu____12998 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13018 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13018
                            in
                         let uu____13025 =
                           let uu____13034 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13054 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13054
                              in
                           let uu____13063 =
                             let uu____13072 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13092 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13092
                                in
                             [uu____13072]  in
                           uu____13034 :: uu____13063  in
                         uu____12998 :: uu____13025  in
                       comb_or uu____12989))
                 | (uu____13123,uu____13124,uu____13125,FStar_Pervasives_Native.Some
                    uu____13126) ->
                     (log_unfolding cfg
                        (fun uu____13194  ->
                           let uu____13195 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13195);
                      (let uu____13196 =
                         let uu____13205 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13225 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13225
                            in
                         let uu____13232 =
                           let uu____13241 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13261 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13261
                              in
                           let uu____13270 =
                             let uu____13279 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13299 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13299
                                in
                             [uu____13279]  in
                           uu____13241 :: uu____13270  in
                         uu____13205 :: uu____13232  in
                       comb_or uu____13196))
                 | uu____13330 ->
                     (log_unfolding cfg
                        (fun uu____13376  ->
                           let uu____13377 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____13378 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____13379 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____13377 uu____13378 uu____13379);
                      (let uu____13380 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___250_13384  ->
                                 match uu___250_13384 with
                                 | FStar_TypeChecker_Env.UnfoldTac  -> false
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____13380))
                  in
               log_unfolding cfg
                 (fun uu____13397  ->
                    let uu____13398 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____13399 = FStar_Range.string_of_range rng  in
                    let uu____13400 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____13398 uu____13399 uu____13400);
               (match res with
                | (false ,uu____13409,uu____13410) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___310_13426 = cfg  in
                      {
                        steps =
                          (let uu___311_13429 = cfg.steps  in
                           {
                             beta = (uu___311_13429.beta);
                             iota = (uu___311_13429.iota);
                             zeta = (uu___311_13429.zeta);
                             weak = (uu___311_13429.weak);
                             hnf = (uu___311_13429.hnf);
                             primops = (uu___311_13429.primops);
                             do_not_unfold_pure_lets =
                               (uu___311_13429.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___311_13429.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___311_13429.pure_subterms_within_computations);
                             simplify = (uu___311_13429.simplify);
                             erase_universes =
                               (uu___311_13429.erase_universes);
                             allow_unbound_universes =
                               (uu___311_13429.allow_unbound_universes);
                             reify_ = (uu___311_13429.reify_);
                             compress_uvars = (uu___311_13429.compress_uvars);
                             no_full_norm = (uu___311_13429.no_full_norm);
                             check_no_uvars = (uu___311_13429.check_no_uvars);
                             unmeta = (uu___311_13429.unmeta);
                             unascribe = (uu___311_13429.unascribe);
                             in_full_norm_request =
                               (uu___311_13429.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___311_13429.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___310_13426.tcenv);
                        debug = (uu___310_13426.debug);
                        delta_level = (uu___310_13426.delta_level);
                        primitive_steps = (uu___310_13426.primitive_steps);
                        strong = (uu___310_13426.strong);
                        memoize_lazy = (uu___310_13426.memoize_lazy);
                        normalize_pure_lets =
                          (uu___310_13426.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____13447 =
                      let uu____13454 = FStar_List.tl stack  in
                      (cfg, uu____13454)  in
                    FStar_Pervasives_Native.Some uu____13447
                | uu____13465 ->
                    let uu____13472 =
                      let uu____13473 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____13473
                       in
                    FStar_All.pipe_left failwith uu____13472))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13781 ->
                   let uu____13804 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13804
               | uu____13805 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13813  ->
               let uu____13814 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13815 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13816 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13823 =
                 let uu____13824 =
                   let uu____13827 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13827
                    in
                 stack_to_string uu____13824  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13814 uu____13815 uu____13816 uu____13823);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____13853  ->
                     let uu____13854 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13854);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____13855 ->
               (log_unfolding cfg
                  (fun uu____13859  ->
                     let uu____13860 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13860);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____13861 ->
               (log_unfolding cfg
                  (fun uu____13865  ->
                     let uu____13866 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13866);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____13867 ->
               (log_unfolding cfg
                  (fun uu____13871  ->
                     let uu____13872 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13872);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13873;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____13874;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____13880  ->
                     let uu____13881 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13881);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13882;
                 FStar_Syntax_Syntax.fv_delta = uu____13883;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____13887  ->
                     let uu____13888 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13888);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13889;
                 FStar_Syntax_Syntax.fv_delta = uu____13890;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13891);_}
               ->
               (log_unfolding cfg
                  (fun uu____13901  ->
                     let uu____13902 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13902);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____13905 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____13905  in
               let uu____13906 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____13906 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____13939 ->
               let uu____13946 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13946
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____13976 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____13976)
               ->
               let cfg' =
                 let uu___312_13978 = cfg  in
                 {
                   steps =
                     (let uu___313_13981 = cfg.steps  in
                      {
                        beta = (uu___313_13981.beta);
                        iota = (uu___313_13981.iota);
                        zeta = (uu___313_13981.zeta);
                        weak = (uu___313_13981.weak);
                        hnf = (uu___313_13981.hnf);
                        primops = (uu___313_13981.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___313_13981.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___313_13981.unfold_attr);
                        unfold_tac = (uu___313_13981.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___313_13981.pure_subterms_within_computations);
                        simplify = (uu___313_13981.simplify);
                        erase_universes = (uu___313_13981.erase_universes);
                        allow_unbound_universes =
                          (uu___313_13981.allow_unbound_universes);
                        reify_ = (uu___313_13981.reify_);
                        compress_uvars = (uu___313_13981.compress_uvars);
                        no_full_norm = (uu___313_13981.no_full_norm);
                        check_no_uvars = (uu___313_13981.check_no_uvars);
                        unmeta = (uu___313_13981.unmeta);
                        unascribe = (uu___313_13981.unascribe);
                        in_full_norm_request =
                          (uu___313_13981.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___313_13981.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___312_13978.tcenv);
                   debug = (uu___312_13978.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___312_13978.primitive_steps);
                   strong = (uu___312_13978.strong);
                   memoize_lazy = (uu___312_13978.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13986 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____13986 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14015  ->
                              fun stack1  ->
                                match uu____14015 with
                                | (a,aq) ->
                                    let uu____14027 =
                                      let uu____14028 =
                                        let uu____14035 =
                                          let uu____14036 =
                                            let uu____14067 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14067, false)  in
                                          Clos uu____14036  in
                                        (uu____14035, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14028  in
                                    uu____14027 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14155  ->
                          let uu____14156 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14156);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14178 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___251_14183  ->
                                match uu___251_14183 with
                                | UnfoldUntil uu____14184 -> true
                                | UnfoldOnly uu____14185 -> true
                                | UnfoldFully uu____14188 -> true
                                | uu____14191 -> false))
                         in
                      if uu____14178
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___314_14196 = cfg  in
                      let uu____14197 =
                        let uu___315_14198 = to_fsteps s  in
                        {
                          beta = (uu___315_14198.beta);
                          iota = (uu___315_14198.iota);
                          zeta = (uu___315_14198.zeta);
                          weak = (uu___315_14198.weak);
                          hnf = (uu___315_14198.hnf);
                          primops = (uu___315_14198.primops);
                          do_not_unfold_pure_lets =
                            (uu___315_14198.do_not_unfold_pure_lets);
                          unfold_until = (uu___315_14198.unfold_until);
                          unfold_only = (uu___315_14198.unfold_only);
                          unfold_fully = (uu___315_14198.unfold_fully);
                          unfold_attr = (uu___315_14198.unfold_attr);
                          unfold_tac = (uu___315_14198.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___315_14198.pure_subterms_within_computations);
                          simplify = (uu___315_14198.simplify);
                          erase_universes = (uu___315_14198.erase_universes);
                          allow_unbound_universes =
                            (uu___315_14198.allow_unbound_universes);
                          reify_ = (uu___315_14198.reify_);
                          compress_uvars = (uu___315_14198.compress_uvars);
                          no_full_norm = (uu___315_14198.no_full_norm);
                          check_no_uvars = (uu___315_14198.check_no_uvars);
                          unmeta = (uu___315_14198.unmeta);
                          unascribe = (uu___315_14198.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___315_14198.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14197;
                        tcenv = (uu___314_14196.tcenv);
                        debug = (uu___314_14196.debug);
                        delta_level;
                        primitive_steps = (uu___314_14196.primitive_steps);
                        strong = (uu___314_14196.strong);
                        memoize_lazy = (uu___314_14196.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14203 =
                          let uu____14204 =
                            let uu____14209 = FStar_Util.now ()  in
                            (t1, uu____14209)  in
                          Debug uu____14204  in
                        uu____14203 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14213 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14213
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14222 =
                      let uu____14229 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14229, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14222  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14238 = lookup_bvar env x  in
               (match uu____14238 with
                | Univ uu____14239 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14288 = FStar_ST.op_Bang r  in
                      (match uu____14288 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14410  ->
                                 let uu____14411 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14412 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14411
                                   uu____14412);
                            (let uu____14413 = maybe_weakly_reduced t'  in
                             if uu____14413
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14414 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14485)::uu____14486 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14496,uu____14497))::stack_rest ->
                    (match c with
                     | Univ uu____14501 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14510 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14531  ->
                                    let uu____14532 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14532);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14560  ->
                                    let uu____14561 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14561);
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
                       (fun uu____14627  ->
                          let uu____14628 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14628);
                     norm cfg env stack1 t1)
                | (Match uu____14629)::uu____14630 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14644 = cfg.steps  in
                             {
                               beta = (uu___316_14644.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14644.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14644.unfold_until);
                               unfold_only = (uu___316_14644.unfold_only);
                               unfold_fully = (uu___316_14644.unfold_fully);
                               unfold_attr = (uu___316_14644.unfold_attr);
                               unfold_tac = (uu___316_14644.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14644.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14644.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14644.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14644.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14644.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14644.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14646 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14646.tcenv);
                               debug = (uu___317_14646.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14646.primitive_steps);
                               strong = (uu___317_14646.strong);
                               memoize_lazy = (uu___317_14646.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14646.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14648 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14648 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14680  -> dummy :: env1) env)
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
                                          let uu____14721 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14721)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_14728 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_14728.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_14728.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14729 -> lopt  in
                           (log cfg
                              (fun uu____14735  ->
                                 let uu____14736 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14736);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_14745 = cfg  in
                               {
                                 steps = (uu___319_14745.steps);
                                 tcenv = (uu___319_14745.tcenv);
                                 debug = (uu___319_14745.debug);
                                 delta_level = (uu___319_14745.delta_level);
                                 primitive_steps =
                                   (uu___319_14745.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_14745.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_14745.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____14748)::uu____14749 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14759 = cfg.steps  in
                             {
                               beta = (uu___316_14759.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14759.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14759.unfold_until);
                               unfold_only = (uu___316_14759.unfold_only);
                               unfold_fully = (uu___316_14759.unfold_fully);
                               unfold_attr = (uu___316_14759.unfold_attr);
                               unfold_tac = (uu___316_14759.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14759.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14759.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14759.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14759.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14759.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14759.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14761 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14761.tcenv);
                               debug = (uu___317_14761.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14761.primitive_steps);
                               strong = (uu___317_14761.strong);
                               memoize_lazy = (uu___317_14761.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14761.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14763 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14763 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14795  -> dummy :: env1) env)
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
                                          let uu____14836 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14836)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_14843 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_14843.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_14843.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14844 -> lopt  in
                           (log cfg
                              (fun uu____14850  ->
                                 let uu____14851 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14851);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_14860 = cfg  in
                               {
                                 steps = (uu___319_14860.steps);
                                 tcenv = (uu___319_14860.tcenv);
                                 debug = (uu___319_14860.debug);
                                 delta_level = (uu___319_14860.delta_level);
                                 primitive_steps =
                                   (uu___319_14860.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_14860.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_14860.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14863)::uu____14864 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14876 = cfg.steps  in
                             {
                               beta = (uu___316_14876.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14876.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14876.unfold_until);
                               unfold_only = (uu___316_14876.unfold_only);
                               unfold_fully = (uu___316_14876.unfold_fully);
                               unfold_attr = (uu___316_14876.unfold_attr);
                               unfold_tac = (uu___316_14876.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14876.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14876.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14876.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14876.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14876.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14876.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14878 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14878.tcenv);
                               debug = (uu___317_14878.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14878.primitive_steps);
                               strong = (uu___317_14878.strong);
                               memoize_lazy = (uu___317_14878.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14878.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14880 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14880 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14912  -> dummy :: env1) env)
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
                                          let uu____14953 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14953)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_14960 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_14960.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_14960.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14961 -> lopt  in
                           (log cfg
                              (fun uu____14967  ->
                                 let uu____14968 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14968);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_14977 = cfg  in
                               {
                                 steps = (uu___319_14977.steps);
                                 tcenv = (uu___319_14977.tcenv);
                                 debug = (uu___319_14977.debug);
                                 delta_level = (uu___319_14977.delta_level);
                                 primitive_steps =
                                   (uu___319_14977.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_14977.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_14977.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14980)::uu____14981 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_14995 = cfg.steps  in
                             {
                               beta = (uu___316_14995.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_14995.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_14995.unfold_until);
                               unfold_only = (uu___316_14995.unfold_only);
                               unfold_fully = (uu___316_14995.unfold_fully);
                               unfold_attr = (uu___316_14995.unfold_attr);
                               unfold_tac = (uu___316_14995.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_14995.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_14995.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_14995.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_14995.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_14995.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_14995.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_14997 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_14997.tcenv);
                               debug = (uu___317_14997.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_14997.primitive_steps);
                               strong = (uu___317_14997.strong);
                               memoize_lazy = (uu___317_14997.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_14997.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14999 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14999 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15031  -> dummy :: env1) env)
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
                                          let uu____15072 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15072)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15079 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15079.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15079.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15080 -> lopt  in
                           (log cfg
                              (fun uu____15086  ->
                                 let uu____15087 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15087);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15096 = cfg  in
                               {
                                 steps = (uu___319_15096.steps);
                                 tcenv = (uu___319_15096.tcenv);
                                 debug = (uu___319_15096.debug);
                                 delta_level = (uu___319_15096.delta_level);
                                 primitive_steps =
                                   (uu___319_15096.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15096.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15096.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15099)::uu____15100 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_15114 = cfg.steps  in
                             {
                               beta = (uu___316_15114.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_15114.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_15114.unfold_until);
                               unfold_only = (uu___316_15114.unfold_only);
                               unfold_fully = (uu___316_15114.unfold_fully);
                               unfold_attr = (uu___316_15114.unfold_attr);
                               unfold_tac = (uu___316_15114.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_15114.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_15114.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_15114.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_15114.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_15114.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_15114.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_15116 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_15116.tcenv);
                               debug = (uu___317_15116.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_15116.primitive_steps);
                               strong = (uu___317_15116.strong);
                               memoize_lazy = (uu___317_15116.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_15116.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15118 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15118 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15150  -> dummy :: env1) env)
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
                                          let uu____15191 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15191)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15198 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15198.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15198.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15199 -> lopt  in
                           (log cfg
                              (fun uu____15205  ->
                                 let uu____15206 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15206);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15215 = cfg  in
                               {
                                 steps = (uu___319_15215.steps);
                                 tcenv = (uu___319_15215.tcenv);
                                 debug = (uu___319_15215.debug);
                                 delta_level = (uu___319_15215.delta_level);
                                 primitive_steps =
                                   (uu___319_15215.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15215.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15215.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15218)::uu____15219 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___316_15237 = cfg.steps  in
                             {
                               beta = (uu___316_15237.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_15237.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_15237.unfold_until);
                               unfold_only = (uu___316_15237.unfold_only);
                               unfold_fully = (uu___316_15237.unfold_fully);
                               unfold_attr = (uu___316_15237.unfold_attr);
                               unfold_tac = (uu___316_15237.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_15237.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_15237.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_15237.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_15237.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_15237.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_15237.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_15239 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_15239.tcenv);
                               debug = (uu___317_15239.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_15239.primitive_steps);
                               strong = (uu___317_15239.strong);
                               memoize_lazy = (uu___317_15239.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_15239.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15241 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15241 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15273  -> dummy :: env1) env)
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
                                          let uu____15314 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15314)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15321 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15321.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15321.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15322 -> lopt  in
                           (log cfg
                              (fun uu____15328  ->
                                 let uu____15329 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15329);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15338 = cfg  in
                               {
                                 steps = (uu___319_15338.steps);
                                 tcenv = (uu___319_15338.tcenv);
                                 debug = (uu___319_15338.debug);
                                 delta_level = (uu___319_15338.delta_level);
                                 primitive_steps =
                                   (uu___319_15338.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15338.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15338.normalize_pure_lets)
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
                             let uu___316_15344 = cfg.steps  in
                             {
                               beta = (uu___316_15344.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___316_15344.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___316_15344.unfold_until);
                               unfold_only = (uu___316_15344.unfold_only);
                               unfold_fully = (uu___316_15344.unfold_fully);
                               unfold_attr = (uu___316_15344.unfold_attr);
                               unfold_tac = (uu___316_15344.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___316_15344.erase_universes);
                               allow_unbound_universes =
                                 (uu___316_15344.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___316_15344.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___316_15344.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___316_15344.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___316_15344.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___317_15346 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___317_15346.tcenv);
                               debug = (uu___317_15346.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___317_15346.primitive_steps);
                               strong = (uu___317_15346.strong);
                               memoize_lazy = (uu___317_15346.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___317_15346.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15348 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15348 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15380  -> dummy :: env1) env)
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
                                          let uu____15421 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15421)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___318_15428 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___318_15428.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___318_15428.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15429 -> lopt  in
                           (log cfg
                              (fun uu____15435  ->
                                 let uu____15436 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15436);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___319_15445 = cfg  in
                               {
                                 steps = (uu___319_15445.steps);
                                 tcenv = (uu___319_15445.tcenv);
                                 debug = (uu___319_15445.debug);
                                 delta_level = (uu___319_15445.delta_level);
                                 primitive_steps =
                                   (uu___319_15445.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___319_15445.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___319_15445.normalize_pure_lets)
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
                      (fun uu____15484  ->
                         fun stack1  ->
                           match uu____15484 with
                           | (a,aq) ->
                               let uu____15496 =
                                 let uu____15497 =
                                   let uu____15504 =
                                     let uu____15505 =
                                       let uu____15536 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15536, false)  in
                                     Clos uu____15505  in
                                   (uu____15504, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15497  in
                               uu____15496 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15624  ->
                     let uu____15625 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15625);
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
                             ((let uu___320_15671 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___320_15671.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___320_15671.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15672 ->
                      let uu____15687 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15687)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15690 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15690 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15715 =
                          let uu____15716 =
                            let uu____15723 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___321_15729 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___321_15729.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___321_15729.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15723)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15716  in
                        mk uu____15715 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15748 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15748
               else
                 (let uu____15750 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15750 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15758 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15780  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15758 c1  in
                      let t2 =
                        let uu____15802 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15802 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15913)::uu____15914 ->
                    (log cfg
                       (fun uu____15927  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15928)::uu____15929 ->
                    (log cfg
                       (fun uu____15940  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15941,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15942;
                                   FStar_Syntax_Syntax.vars = uu____15943;_},uu____15944,uu____15945))::uu____15946
                    ->
                    (log cfg
                       (fun uu____15953  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15954)::uu____15955 ->
                    (log cfg
                       (fun uu____15966  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15967 ->
                    (log cfg
                       (fun uu____15970  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15974  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15999 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15999
                         | FStar_Util.Inr c ->
                             let uu____16013 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16013
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16036 =
                               let uu____16037 =
                                 let uu____16064 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16064, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16037
                                in
                             mk uu____16036 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16099 ->
                           let uu____16100 =
                             let uu____16101 =
                               let uu____16102 =
                                 let uu____16129 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16129, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16102
                                in
                             mk uu____16101 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16100))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___322_16206 = cfg  in
                   {
                     steps =
                       (let uu___323_16209 = cfg.steps  in
                        {
                          beta = (uu___323_16209.beta);
                          iota = (uu___323_16209.iota);
                          zeta = (uu___323_16209.zeta);
                          weak = true;
                          hnf = (uu___323_16209.hnf);
                          primops = (uu___323_16209.primops);
                          do_not_unfold_pure_lets =
                            (uu___323_16209.do_not_unfold_pure_lets);
                          unfold_until = (uu___323_16209.unfold_until);
                          unfold_only = (uu___323_16209.unfold_only);
                          unfold_fully = (uu___323_16209.unfold_fully);
                          unfold_attr = (uu___323_16209.unfold_attr);
                          unfold_tac = (uu___323_16209.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___323_16209.pure_subterms_within_computations);
                          simplify = (uu___323_16209.simplify);
                          erase_universes = (uu___323_16209.erase_universes);
                          allow_unbound_universes =
                            (uu___323_16209.allow_unbound_universes);
                          reify_ = (uu___323_16209.reify_);
                          compress_uvars = (uu___323_16209.compress_uvars);
                          no_full_norm = (uu___323_16209.no_full_norm);
                          check_no_uvars = (uu___323_16209.check_no_uvars);
                          unmeta = (uu___323_16209.unmeta);
                          unascribe = (uu___323_16209.unascribe);
                          in_full_norm_request =
                            (uu___323_16209.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___323_16209.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___322_16206.tcenv);
                     debug = (uu___322_16206.debug);
                     delta_level = (uu___322_16206.delta_level);
                     primitive_steps = (uu___322_16206.primitive_steps);
                     strong = (uu___322_16206.strong);
                     memoize_lazy = (uu___322_16206.memoize_lazy);
                     normalize_pure_lets =
                       (uu___322_16206.normalize_pure_lets)
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
                         let uu____16245 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16245 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___324_16265 = cfg  in
                               let uu____16266 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___324_16265.steps);
                                 tcenv = uu____16266;
                                 debug = (uu___324_16265.debug);
                                 delta_level = (uu___324_16265.delta_level);
                                 primitive_steps =
                                   (uu___324_16265.primitive_steps);
                                 strong = (uu___324_16265.strong);
                                 memoize_lazy = (uu___324_16265.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___324_16265.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16273 =
                                 let uu____16274 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16274  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16273
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___325_16277 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___325_16277.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___325_16277.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___325_16277.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___325_16277.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16278 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16278
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16289,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16290;
                               FStar_Syntax_Syntax.lbunivs = uu____16291;
                               FStar_Syntax_Syntax.lbtyp = uu____16292;
                               FStar_Syntax_Syntax.lbeff = uu____16293;
                               FStar_Syntax_Syntax.lbdef = uu____16294;
                               FStar_Syntax_Syntax.lbattrs = uu____16295;
                               FStar_Syntax_Syntax.lbpos = uu____16296;_}::uu____16297),uu____16298)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16338 =
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
               if uu____16338
               then
                 let binder =
                   let uu____16340 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16340  in
                 let env1 =
                   let uu____16350 =
                     let uu____16357 =
                       let uu____16358 =
                         let uu____16389 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16389,
                           false)
                          in
                       Clos uu____16358  in
                     ((FStar_Pervasives_Native.Some binder), uu____16357)  in
                   uu____16350 :: env  in
                 (log cfg
                    (fun uu____16484  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16488  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16489 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16489))
                 else
                   (let uu____16491 =
                      let uu____16496 =
                        let uu____16497 =
                          let uu____16502 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16502
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16497]  in
                      FStar_Syntax_Subst.open_term uu____16496 body  in
                    match uu____16491 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16523  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16531 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16531  in
                            FStar_Util.Inl
                              (let uu___326_16541 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___326_16541.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___326_16541.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16544  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___327_16546 = lb  in
                             let uu____16547 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___327_16546.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___327_16546.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16547;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___327_16546.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___327_16546.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16572  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___328_16595 = cfg  in
                             {
                               steps = (uu___328_16595.steps);
                               tcenv = (uu___328_16595.tcenv);
                               debug = (uu___328_16595.debug);
                               delta_level = (uu___328_16595.delta_level);
                               primitive_steps =
                                 (uu___328_16595.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___328_16595.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___328_16595.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16598  ->
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
               let uu____16615 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16615 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16651 =
                               let uu___329_16652 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___329_16652.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___329_16652.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16651  in
                           let uu____16653 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16653 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16679 =
                                   FStar_List.map (fun uu____16695  -> dummy)
                                     lbs1
                                    in
                                 let uu____16696 =
                                   let uu____16705 =
                                     FStar_List.map
                                       (fun uu____16725  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16705 env  in
                                 FStar_List.append uu____16679 uu____16696
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16749 =
                                       let uu___330_16750 = rc  in
                                       let uu____16751 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___330_16750.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16751;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___330_16750.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16749
                                 | uu____16760 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___331_16766 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___331_16766.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___331_16766.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___331_16766.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___331_16766.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16776 =
                        FStar_List.map (fun uu____16792  -> dummy) lbs2  in
                      FStar_List.append uu____16776 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16800 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16800 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___332_16816 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___332_16816.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___332_16816.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16845 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16845
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16864 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16940  ->
                        match uu____16940 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___333_17061 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___333_17061.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___333_17061.FStar_Syntax_Syntax.sort)
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
               (match uu____16864 with
                | (rec_env,memos,uu____17288) ->
                    let uu____17341 =
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
                             let uu____17664 =
                               let uu____17671 =
                                 let uu____17672 =
                                   let uu____17703 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17703, false)
                                    in
                                 Clos uu____17672  in
                               (FStar_Pervasives_Native.None, uu____17671)
                                in
                             uu____17664 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17807  ->
                     let uu____17808 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17808);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____17830 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17832::uu____17833 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17838) ->
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
                             | uu____17861 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17875 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17875
                              | uu____17886 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17892 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17916 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17930 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17943 =
                        let uu____17944 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17945 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17944 uu____17945
                         in
                      failwith uu____17943
                    else
                      (let uu____17947 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____17947)
                | uu____17948 -> norm cfg env stack t2))

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
              let uu____17957 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17957 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____17971  ->
                        let uu____17972 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____17972);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____17983  ->
                        let uu____17984 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17985 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____17984 uu____17985);
                   (let t1 =
                      if
                        (cfg.steps).unfold_until =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____17998))::stack1 ->
                          ((let uu____18007 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____18007
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____18011 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____18011) us'
                            else ());
                           (let env1 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env1  ->
                                      fun u  ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env1) env)
                               in
                            norm cfg env1 stack1 t1))
                      | uu____18044 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____18047 ->
                          let uu____18050 =
                            let uu____18051 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____18051
                             in
                          failwith uu____18050
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
                  let uu___334_18075 = cfg  in
                  let uu____18076 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18076;
                    tcenv = (uu___334_18075.tcenv);
                    debug = (uu___334_18075.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___334_18075.primitive_steps);
                    strong = (uu___334_18075.strong);
                    memoize_lazy = (uu___334_18075.memoize_lazy);
                    normalize_pure_lets =
                      (uu___334_18075.normalize_pure_lets)
                  }
                else
                  (let uu___335_18078 = cfg  in
                   {
                     steps =
                       (let uu___336_18081 = cfg.steps  in
                        {
                          beta = (uu___336_18081.beta);
                          iota = (uu___336_18081.iota);
                          zeta = false;
                          weak = (uu___336_18081.weak);
                          hnf = (uu___336_18081.hnf);
                          primops = (uu___336_18081.primops);
                          do_not_unfold_pure_lets =
                            (uu___336_18081.do_not_unfold_pure_lets);
                          unfold_until = (uu___336_18081.unfold_until);
                          unfold_only = (uu___336_18081.unfold_only);
                          unfold_fully = (uu___336_18081.unfold_fully);
                          unfold_attr = (uu___336_18081.unfold_attr);
                          unfold_tac = (uu___336_18081.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___336_18081.pure_subterms_within_computations);
                          simplify = (uu___336_18081.simplify);
                          erase_universes = (uu___336_18081.erase_universes);
                          allow_unbound_universes =
                            (uu___336_18081.allow_unbound_universes);
                          reify_ = (uu___336_18081.reify_);
                          compress_uvars = (uu___336_18081.compress_uvars);
                          no_full_norm = (uu___336_18081.no_full_norm);
                          check_no_uvars = (uu___336_18081.check_no_uvars);
                          unmeta = (uu___336_18081.unmeta);
                          unascribe = (uu___336_18081.unascribe);
                          in_full_norm_request =
                            (uu___336_18081.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___336_18081.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___335_18078.tcenv);
                     debug = (uu___335_18078.debug);
                     delta_level = (uu___335_18078.delta_level);
                     primitive_steps = (uu___335_18078.primitive_steps);
                     strong = (uu___335_18078.strong);
                     memoize_lazy = (uu___335_18078.memoize_lazy);
                     normalize_pure_lets =
                       (uu___335_18078.normalize_pure_lets)
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
                  (fun uu____18115  ->
                     let uu____18116 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18117 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18116
                       uu____18117);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18119 =
                   let uu____18120 = FStar_Syntax_Subst.compress head3  in
                   uu____18120.FStar_Syntax_Syntax.n  in
                 match uu____18119 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18138 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18138
                        in
                     let uu____18139 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18139 with
                      | (uu____18140,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18150 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18160 =
                                   let uu____18161 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18161.FStar_Syntax_Syntax.n  in
                                 match uu____18160 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18167,uu____18168))
                                     ->
                                     let uu____18177 =
                                       let uu____18178 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18178.FStar_Syntax_Syntax.n  in
                                     (match uu____18177 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18184,msrc,uu____18186))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18195 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18195
                                      | uu____18196 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18197 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18198 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18198 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___337_18203 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___337_18203.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___337_18203.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___337_18203.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___337_18203.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___337_18203.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18204 = FStar_List.tl stack  in
                                    let uu____18205 =
                                      let uu____18206 =
                                        let uu____18213 =
                                          let uu____18214 =
                                            let uu____18227 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18227)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18214
                                           in
                                        FStar_Syntax_Syntax.mk uu____18213
                                         in
                                      uu____18206
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18204 uu____18205
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18243 =
                                      let uu____18244 = is_return body  in
                                      match uu____18244 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18248;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18249;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18252 -> false  in
                                    if uu____18243
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
                                         let uu____18273 =
                                           let uu____18280 =
                                             let uu____18281 =
                                               let uu____18298 =
                                                 let uu____18305 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18305]  in
                                               (uu____18298, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18281
                                              in
                                           FStar_Syntax_Syntax.mk uu____18280
                                            in
                                         uu____18273
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18339 =
                                           let uu____18340 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18340.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18339 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18346::uu____18347::[])
                                             ->
                                             let uu____18352 =
                                               let uu____18359 =
                                                 let uu____18360 =
                                                   let uu____18367 =
                                                     let uu____18368 =
                                                       let uu____18369 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18369
                                                        in
                                                     let uu____18370 =
                                                       let uu____18373 =
                                                         let uu____18374 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18374
                                                          in
                                                       [uu____18373]  in
                                                     uu____18368 ::
                                                       uu____18370
                                                      in
                                                   (bind1, uu____18367)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18360
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18359
                                                in
                                             uu____18352
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18380 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18392 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18392
                                         then
                                           let uu____18401 =
                                             let uu____18408 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18408
                                              in
                                           let uu____18409 =
                                             let uu____18418 =
                                               let uu____18425 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18425
                                                in
                                             [uu____18418]  in
                                           uu____18401 :: uu____18409
                                         else []  in
                                       let reified =
                                         let uu____18454 =
                                           let uu____18461 =
                                             let uu____18462 =
                                               let uu____18477 =
                                                 let uu____18486 =
                                                   let uu____18495 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18502 =
                                                     let uu____18511 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18511]  in
                                                   uu____18495 :: uu____18502
                                                    in
                                                 let uu____18536 =
                                                   let uu____18545 =
                                                     let uu____18554 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18561 =
                                                       let uu____18570 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18577 =
                                                         let uu____18586 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18593 =
                                                           let uu____18602 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18602]  in
                                                         uu____18586 ::
                                                           uu____18593
                                                          in
                                                       uu____18570 ::
                                                         uu____18577
                                                        in
                                                     uu____18554 ::
                                                       uu____18561
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18545
                                                    in
                                                 FStar_List.append
                                                   uu____18486 uu____18536
                                                  in
                                               (bind_inst, uu____18477)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18462
                                              in
                                           FStar_Syntax_Syntax.mk uu____18461
                                            in
                                         uu____18454
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18668  ->
                                            let uu____18669 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18670 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18669 uu____18670);
                                       (let uu____18671 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18671 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18695 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18695
                        in
                     let uu____18696 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18696 with
                      | (uu____18697,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18734 =
                                  let uu____18735 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18735.FStar_Syntax_Syntax.n  in
                                match uu____18734 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18739) -> t2
                                | uu____18744 -> head4  in
                              let uu____18745 =
                                let uu____18746 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18746.FStar_Syntax_Syntax.n  in
                              match uu____18745 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18752 -> FStar_Pervasives_Native.None
                               in
                            let uu____18753 = maybe_extract_fv head4  in
                            match uu____18753 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18763 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18763
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18768 = maybe_extract_fv head5
                                     in
                                  match uu____18768 with
                                  | FStar_Pervasives_Native.Some uu____18773
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18774 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18779 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18794 =
                              match uu____18794 with
                              | (e,q) ->
                                  let uu____18801 =
                                    let uu____18802 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18802.FStar_Syntax_Syntax.n  in
                                  (match uu____18801 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____18817 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____18817
                                   | uu____18818 -> false)
                               in
                            let uu____18819 =
                              let uu____18820 =
                                let uu____18829 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18829 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18820
                               in
                            if uu____18819
                            then
                              let uu____18848 =
                                let uu____18849 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18849
                                 in
                              failwith uu____18848
                            else ());
                           (let uu____18851 = maybe_unfold_action head_app
                               in
                            match uu____18851 with
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
                                   (fun uu____18894  ->
                                      let uu____18895 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18896 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18895 uu____18896);
                                 (let uu____18897 = FStar_List.tl stack  in
                                  norm cfg env uu____18897 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18899) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18923 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18923  in
                     (log cfg
                        (fun uu____18927  ->
                           let uu____18928 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18928);
                      (let uu____18929 = FStar_List.tl stack  in
                       norm cfg env uu____18929 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____19050  ->
                               match uu____19050 with
                               | (pat,wopt,tm) ->
                                   let uu____19098 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19098)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19130 = FStar_List.tl stack  in
                     norm cfg env uu____19130 tm
                 | uu____19131 -> fallback ())

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
              (fun uu____19145  ->
                 let uu____19146 = FStar_Ident.string_of_lid msrc  in
                 let uu____19147 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19148 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19146
                   uu____19147 uu____19148);
            (let uu____19149 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19149
             then
               let ed =
                 let uu____19151 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19151  in
               let uu____19152 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19152 with
               | (uu____19153,return_repr) ->
                   let return_inst =
                     let uu____19166 =
                       let uu____19167 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19167.FStar_Syntax_Syntax.n  in
                     match uu____19166 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19173::[]) ->
                         let uu____19178 =
                           let uu____19185 =
                             let uu____19186 =
                               let uu____19193 =
                                 let uu____19194 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19194]  in
                               (return_tm, uu____19193)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19186  in
                           FStar_Syntax_Syntax.mk uu____19185  in
                         uu____19178 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19200 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19203 =
                     let uu____19210 =
                       let uu____19211 =
                         let uu____19226 =
                           let uu____19235 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19242 =
                             let uu____19251 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19251]  in
                           uu____19235 :: uu____19242  in
                         (return_inst, uu____19226)  in
                       FStar_Syntax_Syntax.Tm_app uu____19211  in
                     FStar_Syntax_Syntax.mk uu____19210  in
                   uu____19203 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19290 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19290 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19293 =
                      let uu____19294 = FStar_Ident.text_of_lid msrc  in
                      let uu____19295 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19294 uu____19295
                       in
                    failwith uu____19293
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19296;
                      FStar_TypeChecker_Env.mtarget = uu____19297;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19298;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19320 =
                      let uu____19321 = FStar_Ident.text_of_lid msrc  in
                      let uu____19322 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19321 uu____19322
                       in
                    failwith uu____19320
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19323;
                      FStar_TypeChecker_Env.mtarget = uu____19324;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19325;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____19360 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____19361 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____19360 t FStar_Syntax_Syntax.tun uu____19361))

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
                (fun uu____19417  ->
                   match uu____19417 with
                   | (a,imp) ->
                       let uu____19428 = norm cfg env [] a  in
                       (uu____19428, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____19436  ->
             let uu____19437 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____19438 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____19437 uu____19438);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19462 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____19462
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___338_19465 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___338_19465.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___338_19465.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19487 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____19487
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___339_19490 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___339_19490.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___339_19490.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____19527  ->
                      match uu____19527 with
                      | (a,i) ->
                          let uu____19538 = norm cfg env [] a  in
                          (uu____19538, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___252_19556  ->
                       match uu___252_19556 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____19560 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____19560
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___340_19568 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___341_19571 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___341_19571.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___340_19568.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___340_19568.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19574  ->
        match uu____19574 with
        | (x,imp) ->
            let uu____19577 =
              let uu___342_19578 = x  in
              let uu____19579 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___342_19578.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___342_19578.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19579
              }  in
            (uu____19577, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19585 =
          FStar_List.fold_left
            (fun uu____19619  ->
               fun b  ->
                 match uu____19619 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19585 with | (nbs,uu____19699) -> FStar_List.rev nbs

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
            let uu____19731 =
              let uu___343_19732 = rc  in
              let uu____19733 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___343_19732.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19733;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___343_19732.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19731
        | uu____19742 -> lopt

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
            (let uu____19763 = FStar_Syntax_Print.term_to_string tm  in
             let uu____19764 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____19763
               uu____19764)
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
          let uu____19786 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____19786
          then tm1
          else
            (let w t =
               let uu___344_19800 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___344_19800.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___344_19800.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____19811 =
                 let uu____19812 = FStar_Syntax_Util.unmeta t  in
                 uu____19812.FStar_Syntax_Syntax.n  in
               match uu____19811 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____19819 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____19868)::args1,(bv,uu____19871)::bs1) ->
                   let uu____19905 =
                     let uu____19906 = FStar_Syntax_Subst.compress t  in
                     uu____19906.FStar_Syntax_Syntax.n  in
                   (match uu____19905 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____19910 -> false)
               | ([],[]) -> true
               | (uu____19931,uu____19932) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19973 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19974 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____19973
                    uu____19974)
               else ();
               (let uu____19976 = FStar_Syntax_Util.head_and_args' t  in
                match uu____19976 with
                | (hd1,args) ->
                    let uu____20009 =
                      let uu____20010 = FStar_Syntax_Subst.compress hd1  in
                      uu____20010.FStar_Syntax_Syntax.n  in
                    (match uu____20009 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____20017 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____20018 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____20019 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____20017 uu____20018 uu____20019)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____20021 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____20038 = FStar_Syntax_Print.term_to_string t  in
                  let uu____20039 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____20038
                    uu____20039)
               else ();
               (let uu____20041 = FStar_Syntax_Util.is_squash t  in
                match uu____20041 with
                | FStar_Pervasives_Native.Some (uu____20052,t') ->
                    is_applied bs t'
                | uu____20064 ->
                    let uu____20073 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____20073 with
                     | FStar_Pervasives_Native.Some (uu____20084,t') ->
                         is_applied bs t'
                     | uu____20096 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20120 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20120 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20127)::(q,uu____20129)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20157 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20158 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20157 uu____20158)
                    else ();
                    (let uu____20160 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20160 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20165 =
                           let uu____20166 = FStar_Syntax_Subst.compress p
                              in
                           uu____20166.FStar_Syntax_Syntax.n  in
                         (match uu____20165 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20174 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20174))
                          | uu____20177 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20180)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20197 =
                           let uu____20198 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20198.FStar_Syntax_Syntax.n  in
                         (match uu____20197 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20206 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20206))
                          | uu____20209 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20213 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20213 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20218 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20218 with
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
                                     let uu____20229 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20229))
                               | uu____20232 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____20237)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____20254 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____20254 with
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
                                     let uu____20265 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20265))
                               | uu____20268 -> FStar_Pervasives_Native.None)
                          | uu____20271 -> FStar_Pervasives_Native.None)
                     | uu____20274 -> FStar_Pervasives_Native.None))
               | uu____20277 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____20290 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20290 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____20296)::[],uu____20297,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20308 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____20309 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____20308
                         uu____20309)
                    else ();
                    is_quantified_const bv phi')
               | uu____20311 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____20324 =
                 let uu____20325 = FStar_Syntax_Subst.compress phi  in
                 uu____20325.FStar_Syntax_Syntax.n  in
               match uu____20324 with
               | FStar_Syntax_Syntax.Tm_match (uu____20330,br::brs) ->
                   let uu____20397 = br  in
                   (match uu____20397 with
                    | (uu____20414,uu____20415,e) ->
                        let r =
                          let uu____20436 = simp_t e  in
                          match uu____20436 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____20442 =
                                FStar_List.for_all
                                  (fun uu____20460  ->
                                     match uu____20460 with
                                     | (uu____20473,uu____20474,e') ->
                                         let uu____20488 = simp_t e'  in
                                         uu____20488 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____20442
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____20496 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____20505 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____20505
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____20536 =
                 match uu____20536 with
                 | (t1,q) ->
                     let uu____20549 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____20549 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____20577 -> (t1, q))
                  in
               let uu____20588 = FStar_Syntax_Util.head_and_args t  in
               match uu____20588 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____20654 =
                 let uu____20655 = FStar_Syntax_Util.unmeta ty  in
                 uu____20655.FStar_Syntax_Syntax.n  in
               match uu____20654 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____20659) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____20664,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____20684 -> false  in
             let simplify1 arg =
               let uu____20709 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____20709, arg)  in
             let uu____20718 = is_forall_const tm1  in
             match uu____20718 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____20723 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____20724 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____20723
                       uu____20724)
                  else ();
                  (let uu____20726 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____20726))
             | FStar_Pervasives_Native.None  ->
                 let uu____20727 =
                   let uu____20728 = FStar_Syntax_Subst.compress tm1  in
                   uu____20728.FStar_Syntax_Syntax.n  in
                 (match uu____20727 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____20732;
                              FStar_Syntax_Syntax.vars = uu____20733;_},uu____20734);
                         FStar_Syntax_Syntax.pos = uu____20735;
                         FStar_Syntax_Syntax.vars = uu____20736;_},args)
                      ->
                      let uu____20762 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20762
                      then
                        let uu____20763 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20763 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20808)::
                             (uu____20809,(arg,uu____20811))::[] ->
                             maybe_auto_squash arg
                         | (uu____20860,(arg,uu____20862))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20863)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20912)::uu____20913::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20964::(FStar_Pervasives_Native.Some (false
                                         ),uu____20965)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21016 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21030 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21030
                         then
                           let uu____21031 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21031 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21076)::uu____21077::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21128::(FStar_Pervasives_Native.Some (true
                                           ),uu____21129)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21180)::(uu____21181,(arg,uu____21183))::[]
                               -> maybe_auto_squash arg
                           | (uu____21232,(arg,uu____21234))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21235)::[]
                               -> maybe_auto_squash arg
                           | uu____21284 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21298 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21298
                            then
                              let uu____21299 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21299 with
                              | uu____21344::(FStar_Pervasives_Native.Some
                                              (true ),uu____21345)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21396)::uu____21397::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21448)::(uu____21449,(arg,uu____21451))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21500,(p,uu____21502))::(uu____21503,
                                                                (q,uu____21505))::[]
                                  ->
                                  let uu____21552 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21552
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21554 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21568 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21568
                               then
                                 let uu____21569 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21569 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21614)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21615)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21666)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21667)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21718)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21719)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21770)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21771)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21822,(arg,uu____21824))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21825)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21874)::(uu____21875,(arg,uu____21877))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21926,(arg,uu____21928))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21929)::[]
                                     ->
                                     let uu____21978 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21978
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21979)::(uu____21980,(arg,uu____21982))::[]
                                     ->
                                     let uu____22031 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22031
                                 | (uu____22032,(p,uu____22034))::(uu____22035,
                                                                   (q,uu____22037))::[]
                                     ->
                                     let uu____22084 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22084
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22086 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22100 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22100
                                  then
                                    let uu____22101 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22101 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22146)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22177)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22208 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22222 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22222
                                     then
                                       match args with
                                       | (t,uu____22224)::[] ->
                                           let uu____22241 =
                                             let uu____22242 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22242.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22241 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22245::[],body,uu____22247)
                                                ->
                                                let uu____22274 = simp_t body
                                                   in
                                                (match uu____22274 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22277 -> tm1)
                                            | uu____22280 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22282))::(t,uu____22284)::[]
                                           ->
                                           let uu____22311 =
                                             let uu____22312 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22312.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22311 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22315::[],body,uu____22317)
                                                ->
                                                let uu____22344 = simp_t body
                                                   in
                                                (match uu____22344 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22347 -> tm1)
                                            | uu____22350 -> tm1)
                                       | uu____22351 -> tm1
                                     else
                                       (let uu____22361 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22361
                                        then
                                          match args with
                                          | (t,uu____22363)::[] ->
                                              let uu____22380 =
                                                let uu____22381 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22381.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22380 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22384::[],body,uu____22386)
                                                   ->
                                                   let uu____22413 =
                                                     simp_t body  in
                                                   (match uu____22413 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22416 -> tm1)
                                               | uu____22419 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22421))::(t,uu____22423)::[]
                                              ->
                                              let uu____22450 =
                                                let uu____22451 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22451.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22450 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22454::[],body,uu____22456)
                                                   ->
                                                   let uu____22483 =
                                                     simp_t body  in
                                                   (match uu____22483 with
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
                                                    | uu____22486 -> tm1)
                                               | uu____22489 -> tm1)
                                          | uu____22490 -> tm1
                                        else
                                          (let uu____22500 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22500
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22501;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22502;_},uu____22503)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22520;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22521;_},uu____22522)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22539 -> tm1
                                           else
                                             (let uu____22549 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22549 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22569 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22579;
                         FStar_Syntax_Syntax.vars = uu____22580;_},args)
                      ->
                      let uu____22602 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22602
                      then
                        let uu____22603 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22603 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22648)::
                             (uu____22649,(arg,uu____22651))::[] ->
                             maybe_auto_squash arg
                         | (uu____22700,(arg,uu____22702))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22703)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22752)::uu____22753::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22804::(FStar_Pervasives_Native.Some (false
                                         ),uu____22805)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22856 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22870 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22870
                         then
                           let uu____22871 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22871 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22916)::uu____22917::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22968::(FStar_Pervasives_Native.Some (true
                                           ),uu____22969)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____23020)::(uu____23021,(arg,uu____23023))::[]
                               -> maybe_auto_squash arg
                           | (uu____23072,(arg,uu____23074))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____23075)::[]
                               -> maybe_auto_squash arg
                           | uu____23124 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23138 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23138
                            then
                              let uu____23139 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23139 with
                              | uu____23184::(FStar_Pervasives_Native.Some
                                              (true ),uu____23185)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23236)::uu____23237::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23288)::(uu____23289,(arg,uu____23291))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23340,(p,uu____23342))::(uu____23343,
                                                                (q,uu____23345))::[]
                                  ->
                                  let uu____23392 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23392
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23394 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23408 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23408
                               then
                                 let uu____23409 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23409 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23454)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23455)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23506)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23507)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23558)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23559)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23610)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23611)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23662,(arg,uu____23664))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23665)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23714)::(uu____23715,(arg,uu____23717))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23766,(arg,uu____23768))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23769)::[]
                                     ->
                                     let uu____23818 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23818
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23819)::(uu____23820,(arg,uu____23822))::[]
                                     ->
                                     let uu____23871 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23871
                                 | (uu____23872,(p,uu____23874))::(uu____23875,
                                                                   (q,uu____23877))::[]
                                     ->
                                     let uu____23924 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23924
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23926 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23940 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23940
                                  then
                                    let uu____23941 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23941 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23986)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24017)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24048 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24062 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24062
                                     then
                                       match args with
                                       | (t,uu____24064)::[] ->
                                           let uu____24081 =
                                             let uu____24082 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24082.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24081 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24085::[],body,uu____24087)
                                                ->
                                                let uu____24114 = simp_t body
                                                   in
                                                (match uu____24114 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24117 -> tm1)
                                            | uu____24120 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24122))::(t,uu____24124)::[]
                                           ->
                                           let uu____24151 =
                                             let uu____24152 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24152.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24151 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24155::[],body,uu____24157)
                                                ->
                                                let uu____24184 = simp_t body
                                                   in
                                                (match uu____24184 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24187 -> tm1)
                                            | uu____24190 -> tm1)
                                       | uu____24191 -> tm1
                                     else
                                       (let uu____24201 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24201
                                        then
                                          match args with
                                          | (t,uu____24203)::[] ->
                                              let uu____24220 =
                                                let uu____24221 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24221.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24220 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24224::[],body,uu____24226)
                                                   ->
                                                   let uu____24253 =
                                                     simp_t body  in
                                                   (match uu____24253 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24256 -> tm1)
                                               | uu____24259 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24261))::(t,uu____24263)::[]
                                              ->
                                              let uu____24290 =
                                                let uu____24291 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24291.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24290 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24294::[],body,uu____24296)
                                                   ->
                                                   let uu____24323 =
                                                     simp_t body  in
                                                   (match uu____24323 with
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
                                                    | uu____24326 -> tm1)
                                               | uu____24329 -> tm1)
                                          | uu____24330 -> tm1
                                        else
                                          (let uu____24340 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24340
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24341;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24342;_},uu____24343)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24360;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24361;_},uu____24362)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24379 -> tm1
                                           else
                                             (let uu____24389 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24389 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24409 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24424 = simp_t t  in
                      (match uu____24424 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24427 ->
                      let uu____24450 = is_const_match tm1  in
                      (match uu____24450 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24453 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____24463  ->
               (let uu____24465 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24466 = FStar_Syntax_Print.term_to_string t  in
                let uu____24467 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24474 =
                  let uu____24475 =
                    let uu____24478 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24478
                     in
                  stack_to_string uu____24475  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24465 uu____24466 uu____24467 uu____24474);
               (let uu____24501 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24501
                then
                  let uu____24502 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24502 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24509 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24510 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24511 =
                          let uu____24512 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24512
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24509
                          uu____24510 uu____24511);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____24530 =
                     let uu____24531 =
                       let uu____24532 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____24532  in
                     FStar_Util.string_of_int uu____24531  in
                   let uu____24537 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____24538 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____24530 uu____24537 uu____24538)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____24544,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____24595  ->
                     let uu____24596 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____24596);
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
               let uu____24634 =
                 let uu___345_24635 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___345_24635.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___345_24635.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____24634
           | (Arg (Univ uu____24638,uu____24639,uu____24640))::uu____24641 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____24644,uu____24645))::uu____24646 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____24661,uu____24662),aq,r))::stack1
               when
               let uu____24712 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24712 ->
               let t2 =
                 let uu____24716 =
                   let uu____24721 =
                     let uu____24722 = closure_as_term cfg env_arg tm  in
                     (uu____24722, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____24721  in
                 uu____24716 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____24732),aq,r))::stack1 ->
               (log cfg
                  (fun uu____24785  ->
                     let uu____24786 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____24786);
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
                  (let uu____24798 = FStar_ST.op_Bang m  in
                   match uu____24798 with
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
                   | FStar_Pervasives_Native.Some (uu____24941,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____24994 =
                 log cfg
                   (fun uu____24998  ->
                      let uu____24999 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____24999);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____25005 =
                 let uu____25006 = FStar_Syntax_Subst.compress t1  in
                 uu____25006.FStar_Syntax_Syntax.n  in
               (match uu____25005 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____25033 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____25033  in
                    (log cfg
                       (fun uu____25037  ->
                          let uu____25038 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____25038);
                     (let uu____25039 = FStar_List.tl stack  in
                      norm cfg env1 uu____25039 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____25040);
                       FStar_Syntax_Syntax.pos = uu____25041;
                       FStar_Syntax_Syntax.vars = uu____25042;_},(e,uu____25044)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____25073 when
                    (cfg.steps).primops ->
                    let uu____25088 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____25088 with
                     | (hd1,args) ->
                         let uu____25125 =
                           let uu____25126 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____25126.FStar_Syntax_Syntax.n  in
                         (match uu____25125 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____25130 = find_prim_step cfg fv  in
                              (match uu____25130 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____25133; arity = uu____25134;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____25136;
                                     requires_binder_substitution =
                                       uu____25137;
                                     interpretation = uu____25138;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____25153 -> fallback " (3)" ())
                          | uu____25156 -> fallback " (4)" ()))
                | uu____25157 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____25180  ->
                     let uu____25181 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____25181);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____25190 =
                   log cfg1
                     (fun uu____25195  ->
                        let uu____25196 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____25197 =
                          let uu____25198 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____25225  ->
                                    match uu____25225 with
                                    | (p,uu____25235,uu____25236) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____25198
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____25196 uu____25197);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___253_25253  ->
                                match uu___253_25253 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____25254 -> false))
                         in
                      let steps =
                        let uu___346_25256 = cfg1.steps  in
                        {
                          beta = (uu___346_25256.beta);
                          iota = (uu___346_25256.iota);
                          zeta = false;
                          weak = (uu___346_25256.weak);
                          hnf = (uu___346_25256.hnf);
                          primops = (uu___346_25256.primops);
                          do_not_unfold_pure_lets =
                            (uu___346_25256.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___346_25256.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___346_25256.pure_subterms_within_computations);
                          simplify = (uu___346_25256.simplify);
                          erase_universes = (uu___346_25256.erase_universes);
                          allow_unbound_universes =
                            (uu___346_25256.allow_unbound_universes);
                          reify_ = (uu___346_25256.reify_);
                          compress_uvars = (uu___346_25256.compress_uvars);
                          no_full_norm = (uu___346_25256.no_full_norm);
                          check_no_uvars = (uu___346_25256.check_no_uvars);
                          unmeta = (uu___346_25256.unmeta);
                          unascribe = (uu___346_25256.unascribe);
                          in_full_norm_request =
                            (uu___346_25256.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___346_25256.weakly_reduce_scrutinee)
                        }  in
                      let uu___347_25261 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___347_25261.tcenv);
                        debug = (uu___347_25261.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___347_25261.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___347_25261.memoize_lazy);
                        normalize_pure_lets =
                          (uu___347_25261.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____25333 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____25362 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____25446  ->
                                    fun uu____25447  ->
                                      match (uu____25446, uu____25447) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____25586 = norm_pat env3 p1
                                             in
                                          (match uu____25586 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____25362 with
                           | (pats1,env3) ->
                               ((let uu___348_25748 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___348_25748.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___349_25767 = x  in
                            let uu____25768 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___349_25767.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___349_25767.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25768
                            }  in
                          ((let uu___350_25782 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___350_25782.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___351_25793 = x  in
                            let uu____25794 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___351_25793.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___351_25793.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25794
                            }  in
                          ((let uu___352_25808 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___352_25808.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___353_25824 = x  in
                            let uu____25825 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___353_25824.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___353_25824.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25825
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___354_25840 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___354_25840.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____25884 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____25914 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____25914 with
                                  | (p,wopt,e) ->
                                      let uu____25934 = norm_pat env1 p  in
                                      (match uu____25934 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____25989 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____25989
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____26006 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____26006
                      then
                        norm
                          (let uu___355_26011 = cfg1  in
                           {
                             steps =
                               (let uu___356_26014 = cfg1.steps  in
                                {
                                  beta = (uu___356_26014.beta);
                                  iota = (uu___356_26014.iota);
                                  zeta = (uu___356_26014.zeta);
                                  weak = (uu___356_26014.weak);
                                  hnf = (uu___356_26014.hnf);
                                  primops = (uu___356_26014.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___356_26014.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___356_26014.unfold_until);
                                  unfold_only = (uu___356_26014.unfold_only);
                                  unfold_fully =
                                    (uu___356_26014.unfold_fully);
                                  unfold_attr = (uu___356_26014.unfold_attr);
                                  unfold_tac = (uu___356_26014.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___356_26014.pure_subterms_within_computations);
                                  simplify = (uu___356_26014.simplify);
                                  erase_universes =
                                    (uu___356_26014.erase_universes);
                                  allow_unbound_universes =
                                    (uu___356_26014.allow_unbound_universes);
                                  reify_ = (uu___356_26014.reify_);
                                  compress_uvars =
                                    (uu___356_26014.compress_uvars);
                                  no_full_norm =
                                    (uu___356_26014.no_full_norm);
                                  check_no_uvars =
                                    (uu___356_26014.check_no_uvars);
                                  unmeta = (uu___356_26014.unmeta);
                                  unascribe = (uu___356_26014.unascribe);
                                  in_full_norm_request =
                                    (uu___356_26014.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___355_26011.tcenv);
                             debug = (uu___355_26011.debug);
                             delta_level = (uu___355_26011.delta_level);
                             primitive_steps =
                               (uu___355_26011.primitive_steps);
                             strong = (uu___355_26011.strong);
                             memoize_lazy = (uu___355_26011.memoize_lazy);
                             normalize_pure_lets =
                               (uu___355_26011.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____26016 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____26016)
                    in
                 let rec is_cons head1 =
                   let uu____26041 =
                     let uu____26042 = FStar_Syntax_Subst.compress head1  in
                     uu____26042.FStar_Syntax_Syntax.n  in
                   match uu____26041 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____26046) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____26051 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____26052;
                         FStar_Syntax_Syntax.fv_delta = uu____26053;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____26054;
                         FStar_Syntax_Syntax.fv_delta = uu____26055;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____26056);_}
                       -> true
                   | uu____26063 -> false  in
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
                   let uu____26226 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____26226 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____26313 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____26352 ->
                                 let uu____26353 =
                                   let uu____26354 = is_cons head1  in
                                   Prims.op_Negation uu____26354  in
                                 FStar_Util.Inr uu____26353)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____26379 =
                              let uu____26380 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____26380.FStar_Syntax_Syntax.n  in
                            (match uu____26379 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____26398 ->
                                 let uu____26399 =
                                   let uu____26400 = is_cons head1  in
                                   Prims.op_Negation uu____26400  in
                                 FStar_Util.Inr uu____26399))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____26477)::rest_a,(p1,uu____26480)::rest_p) ->
                       let uu____26524 = matches_pat t2 p1  in
                       (match uu____26524 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____26573 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____26691 = matches_pat scrutinee1 p1  in
                       (match uu____26691 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____26731  ->
                                  let uu____26732 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____26733 =
                                    let uu____26734 =
                                      FStar_List.map
                                        (fun uu____26744  ->
                                           match uu____26744 with
                                           | (uu____26749,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____26734
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____26732 uu____26733);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____26781  ->
                                       match uu____26781 with
                                       | (bv,t2) ->
                                           let uu____26804 =
                                             let uu____26811 =
                                               let uu____26814 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____26814
                                                in
                                             let uu____26815 =
                                               let uu____26816 =
                                                 let uu____26847 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____26847, false)
                                                  in
                                               Clos uu____26816  in
                                             (uu____26811, uu____26815)  in
                                           uu____26804 :: env2) env1 s
                                 in
                              let uu____26960 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____26960)))
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
    let uu____26987 =
      let uu____26990 = FStar_ST.op_Bang plugins  in p :: uu____26990  in
    FStar_ST.op_Colon_Equals plugins uu____26987  in
  let retrieve uu____27098 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____27175  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___254_27216  ->
                  match uu___254_27216 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____27220 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____27226 -> d  in
        let uu____27229 = to_fsteps s  in
        let uu____27230 =
          let uu____27231 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____27232 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____27233 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____27234 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____27235 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____27236 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____27237 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____27231;
            primop = uu____27232;
            unfolding = uu____27233;
            b380 = uu____27234;
            wpe = uu____27235;
            norm_delayed = uu____27236;
            print_normalized = uu____27237
          }  in
        let uu____27238 =
          let uu____27241 =
            let uu____27244 = retrieve_plugins ()  in
            FStar_List.append uu____27244 psteps  in
          add_steps built_in_primitive_steps uu____27241  in
        let uu____27247 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____27249 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____27249)
           in
        {
          steps = uu____27229;
          tcenv = e;
          debug = uu____27230;
          delta_level = d1;
          primitive_steps = uu____27238;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____27247
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
      fun t  -> let uu____27331 = config s e  in norm_comp uu____27331 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27348 = config [] env  in norm_universe uu____27348 [] u
  
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
        let uu____27372 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27372  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27379 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___357_27398 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___357_27398.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___357_27398.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27405 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27405
          then
            let ct1 =
              let uu____27407 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27407 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____27414 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27414
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___358_27418 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___358_27418.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___358_27418.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___358_27418.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___359_27420 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___359_27420.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___359_27420.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___359_27420.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___359_27420.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___360_27421 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___360_27421.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___360_27421.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27423 -> c
  
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
        let uu____27441 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27441  in
      let uu____27448 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____27448
      then
        let uu____27449 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____27449 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____27455  ->
                 let uu____27456 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____27456)
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
            ((let uu____27477 =
                let uu____27482 =
                  let uu____27483 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27483
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27482)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27477);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____27498 = config [AllowUnboundUniverses] env  in
          norm_comp uu____27498 [] c
        with
        | e ->
            ((let uu____27511 =
                let uu____27516 =
                  let uu____27517 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27517
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27516)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27511);
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
                   let uu____27562 =
                     let uu____27563 =
                       let uu____27570 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27570)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27563  in
                   mk uu____27562 t01.FStar_Syntax_Syntax.pos
               | uu____27575 -> t2)
          | uu____27576 -> t2  in
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
        let uu____27640 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27640 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27669 ->
                 let uu____27676 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27676 with
                  | (actuals,uu____27686,uu____27687) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27701 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27701 with
                         | (binders,args) ->
                             let uu____27712 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27712
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
      | uu____27726 ->
          let uu____27727 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27727 with
           | (head1,args) ->
               let uu____27764 =
                 let uu____27765 = FStar_Syntax_Subst.compress head1  in
                 uu____27765.FStar_Syntax_Syntax.n  in
               (match uu____27764 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27786 =
                      let uu____27799 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27799  in
                    (match uu____27786 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27829 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___365_27837 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___365_27837.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___365_27837.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___365_27837.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___365_27837.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___365_27837.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___365_27837.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___365_27837.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___365_27837.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___365_27837.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___365_27837.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___365_27837.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___365_27837.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___365_27837.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___365_27837.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___365_27837.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___365_27837.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___365_27837.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___365_27837.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___365_27837.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___365_27837.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___365_27837.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___365_27837.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___365_27837.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___365_27837.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___365_27837.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___365_27837.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___365_27837.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___365_27837.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___365_27837.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___365_27837.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___365_27837.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___365_27837.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___365_27837.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___365_27837.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___365_27837.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___365_27837.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____27829 with
                            | (uu____27838,ty,uu____27840) ->
                                eta_expand_with_type env t ty))
                | uu____27841 ->
                    let uu____27842 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___366_27850 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___366_27850.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___366_27850.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___366_27850.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___366_27850.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___366_27850.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___366_27850.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___366_27850.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___366_27850.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___366_27850.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___366_27850.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___366_27850.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___366_27850.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___366_27850.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___366_27850.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___366_27850.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___366_27850.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___366_27850.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___366_27850.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___366_27850.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___366_27850.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___366_27850.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___366_27850.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___366_27850.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___366_27850.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___366_27850.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___366_27850.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___366_27850.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___366_27850.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___366_27850.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___366_27850.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___366_27850.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___366_27850.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___366_27850.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___366_27850.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___366_27850.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___366_27850.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____27842 with
                     | (uu____27851,ty,uu____27853) ->
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
      let uu___367_27926 = x  in
      let uu____27927 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___367_27926.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___367_27926.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27927
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27930 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27953 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27954 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27955 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27956 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27963 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27964 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27965 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___368_27995 = rc  in
          let uu____27996 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28005 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___368_27995.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27996;
            FStar_Syntax_Syntax.residual_flags = uu____28005
          }  in
        let uu____28008 =
          let uu____28009 =
            let uu____28026 = elim_delayed_subst_binders bs  in
            let uu____28033 = elim_delayed_subst_term t2  in
            let uu____28036 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28026, uu____28033, uu____28036)  in
          FStar_Syntax_Syntax.Tm_abs uu____28009  in
        mk1 uu____28008
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28067 =
          let uu____28068 =
            let uu____28081 = elim_delayed_subst_binders bs  in
            let uu____28088 = elim_delayed_subst_comp c  in
            (uu____28081, uu____28088)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28068  in
        mk1 uu____28067
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28105 =
          let uu____28106 =
            let uu____28113 = elim_bv bv  in
            let uu____28114 = elim_delayed_subst_term phi  in
            (uu____28113, uu____28114)  in
          FStar_Syntax_Syntax.Tm_refine uu____28106  in
        mk1 uu____28105
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28141 =
          let uu____28142 =
            let uu____28157 = elim_delayed_subst_term t2  in
            let uu____28160 = elim_delayed_subst_args args  in
            (uu____28157, uu____28160)  in
          FStar_Syntax_Syntax.Tm_app uu____28142  in
        mk1 uu____28141
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___369_28228 = p  in
              let uu____28229 =
                let uu____28230 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28230  in
              {
                FStar_Syntax_Syntax.v = uu____28229;
                FStar_Syntax_Syntax.p =
                  (uu___369_28228.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___370_28232 = p  in
              let uu____28233 =
                let uu____28234 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28234  in
              {
                FStar_Syntax_Syntax.v = uu____28233;
                FStar_Syntax_Syntax.p =
                  (uu___370_28232.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___371_28241 = p  in
              let uu____28242 =
                let uu____28243 =
                  let uu____28250 = elim_bv x  in
                  let uu____28251 = elim_delayed_subst_term t0  in
                  (uu____28250, uu____28251)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28243  in
              {
                FStar_Syntax_Syntax.v = uu____28242;
                FStar_Syntax_Syntax.p =
                  (uu___371_28241.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___372_28274 = p  in
              let uu____28275 =
                let uu____28276 =
                  let uu____28289 =
                    FStar_List.map
                      (fun uu____28312  ->
                         match uu____28312 with
                         | (x,b) ->
                             let uu____28325 = elim_pat x  in
                             (uu____28325, b)) pats
                     in
                  (fv, uu____28289)  in
                FStar_Syntax_Syntax.Pat_cons uu____28276  in
              {
                FStar_Syntax_Syntax.v = uu____28275;
                FStar_Syntax_Syntax.p =
                  (uu___372_28274.FStar_Syntax_Syntax.p)
              }
          | uu____28338 -> p  in
        let elim_branch uu____28362 =
          match uu____28362 with
          | (pat,wopt,t3) ->
              let uu____28388 = elim_pat pat  in
              let uu____28391 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28394 = elim_delayed_subst_term t3  in
              (uu____28388, uu____28391, uu____28394)
           in
        let uu____28399 =
          let uu____28400 =
            let uu____28423 = elim_delayed_subst_term t2  in
            let uu____28426 = FStar_List.map elim_branch branches  in
            (uu____28423, uu____28426)  in
          FStar_Syntax_Syntax.Tm_match uu____28400  in
        mk1 uu____28399
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28557 =
          match uu____28557 with
          | (tc,topt) ->
              let uu____28592 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28602 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28602
                | FStar_Util.Inr c ->
                    let uu____28604 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28604
                 in
              let uu____28605 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28592, uu____28605)
           in
        let uu____28614 =
          let uu____28615 =
            let uu____28642 = elim_delayed_subst_term t2  in
            let uu____28645 = elim_ascription a  in
            (uu____28642, uu____28645, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28615  in
        mk1 uu____28614
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___373_28706 = lb  in
          let uu____28707 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28710 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___373_28706.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___373_28706.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28707;
            FStar_Syntax_Syntax.lbeff =
              (uu___373_28706.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28710;
            FStar_Syntax_Syntax.lbattrs =
              (uu___373_28706.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___373_28706.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28713 =
          let uu____28714 =
            let uu____28727 =
              let uu____28734 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28734)  in
            let uu____28743 = elim_delayed_subst_term t2  in
            (uu____28727, uu____28743)  in
          FStar_Syntax_Syntax.Tm_let uu____28714  in
        mk1 uu____28713
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28787 =
          let uu____28788 =
            let uu____28795 = elim_delayed_subst_term tm  in
            (uu____28795, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28788  in
        mk1 uu____28787
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28806 =
          let uu____28807 =
            let uu____28814 = elim_delayed_subst_term t2  in
            let uu____28817 = elim_delayed_subst_meta md  in
            (uu____28814, uu____28817)  in
          FStar_Syntax_Syntax.Tm_meta uu____28807  in
        mk1 uu____28806

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___255_28826  ->
         match uu___255_28826 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28830 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28830
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
        let uu____28853 =
          let uu____28854 =
            let uu____28863 = elim_delayed_subst_term t  in
            (uu____28863, uopt)  in
          FStar_Syntax_Syntax.Total uu____28854  in
        mk1 uu____28853
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28880 =
          let uu____28881 =
            let uu____28890 = elim_delayed_subst_term t  in
            (uu____28890, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28881  in
        mk1 uu____28880
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___374_28899 = ct  in
          let uu____28900 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28903 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28912 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___374_28899.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___374_28899.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28900;
            FStar_Syntax_Syntax.effect_args = uu____28903;
            FStar_Syntax_Syntax.flags = uu____28912
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___256_28915  ->
    match uu___256_28915 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____28927 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____28927
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28960 =
          let uu____28967 = elim_delayed_subst_term t  in (m, uu____28967)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28960
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28979 =
          let uu____28988 = elim_delayed_subst_term t  in
          (m1, m2, uu____28988)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28979
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____29015  ->
         match uu____29015 with
         | (t,q) ->
             let uu____29026 = elim_delayed_subst_term t  in (uu____29026, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29046  ->
         match uu____29046 with
         | (x,q) ->
             let uu____29057 =
               let uu___375_29058 = x  in
               let uu____29059 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___375_29058.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___375_29058.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29059
               }  in
             (uu____29057, q)) bs

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
            | (uu____29151,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29177,FStar_Util.Inl t) ->
                let uu____29195 =
                  let uu____29202 =
                    let uu____29203 =
                      let uu____29216 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29216)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29203  in
                  FStar_Syntax_Syntax.mk uu____29202  in
                uu____29195 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29230 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29230 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29260 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29323 ->
                    let uu____29324 =
                      let uu____29333 =
                        let uu____29334 = FStar_Syntax_Subst.compress t4  in
                        uu____29334.FStar_Syntax_Syntax.n  in
                      (uu____29333, tc)  in
                    (match uu____29324 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29361) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29402) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29441,FStar_Util.Inl uu____29442) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29469 -> failwith "Impossible")
                 in
              (match uu____29260 with
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
          let uu____29594 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29594 with
          | (univ_names1,binders1,tc) ->
              let uu____29660 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29660)
  
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
          let uu____29709 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29709 with
          | (univ_names1,binders1,tc) ->
              let uu____29775 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29775)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29814 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29814 with
           | (univ_names1,binders1,typ1) ->
               let uu___376_29848 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___376_29848.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___376_29848.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___376_29848.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___376_29848.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___377_29863 = s  in
          let uu____29864 =
            let uu____29865 =
              let uu____29874 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29874, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29865  in
          {
            FStar_Syntax_Syntax.sigel = uu____29864;
            FStar_Syntax_Syntax.sigrng =
              (uu___377_29863.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___377_29863.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___377_29863.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___377_29863.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29891 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29891 with
           | (univ_names1,uu____29911,typ1) ->
               let uu___378_29929 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___378_29929.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___378_29929.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___378_29929.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___378_29929.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29935 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29935 with
           | (univ_names1,uu____29955,typ1) ->
               let uu___379_29973 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_29973.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_29973.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_29973.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_29973.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30001 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30001 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30026 =
                            let uu____30027 =
                              let uu____30028 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____30028  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30027
                             in
                          elim_delayed_subst_term uu____30026  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___380_30031 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___380_30031.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___380_30031.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___380_30031.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___380_30031.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___381_30032 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___381_30032.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_30032.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_30032.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_30032.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___382_30038 = s  in
          let uu____30039 =
            let uu____30040 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____30040  in
          {
            FStar_Syntax_Syntax.sigel = uu____30039;
            FStar_Syntax_Syntax.sigrng =
              (uu___382_30038.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_30038.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_30038.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_30038.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30044 = elim_uvars_aux_t env us [] t  in
          (match uu____30044 with
           | (us1,uu____30064,t1) ->
               let uu___383_30082 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_30082.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_30082.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_30082.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_30082.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____30083 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30085 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____30085 with
           | (univs1,binders,signature) ->
               let uu____30119 =
                 let uu____30124 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30124 with
                 | (univs_opening,univs2) ->
                     let uu____30147 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30147)
                  in
               (match uu____30119 with
                | (univs_opening,univs_closing) ->
                    let uu____30150 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30156 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30157 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30156, uu____30157)  in
                    (match uu____30150 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30181 =
                           match uu____30181 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30199 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30199 with
                                | (us1,t1) ->
                                    let uu____30210 =
                                      let uu____30219 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30230 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30219, uu____30230)  in
                                    (match uu____30210 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30259 =
                                           let uu____30268 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____30279 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____30268, uu____30279)  in
                                         (match uu____30259 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30309 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30309
                                                 in
                                              let uu____30310 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30310 with
                                               | (uu____30333,uu____30334,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30353 =
                                                       let uu____30354 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30354
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30353
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30363 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30363 with
                           | (uu____30380,uu____30381,t1) -> t1  in
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
                             | uu____30451 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30476 =
                               let uu____30477 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30477.FStar_Syntax_Syntax.n  in
                             match uu____30476 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30536 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30567 =
                               let uu____30568 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30568.FStar_Syntax_Syntax.n  in
                             match uu____30567 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30589) ->
                                 let uu____30610 = destruct_action_body body
                                    in
                                 (match uu____30610 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30655 ->
                                 let uu____30656 = destruct_action_body t  in
                                 (match uu____30656 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30705 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30705 with
                           | (action_univs,t) ->
                               let uu____30714 = destruct_action_typ_templ t
                                  in
                               (match uu____30714 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___384_30755 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___384_30755.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___384_30755.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___385_30757 = ed  in
                           let uu____30758 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30759 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30760 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30761 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30762 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30763 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30764 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____30765 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____30766 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____30767 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30768 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____30769 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30770 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30771 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___385_30757.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___385_30757.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____30758;
                             FStar_Syntax_Syntax.bind_wp = uu____30759;
                             FStar_Syntax_Syntax.if_then_else = uu____30760;
                             FStar_Syntax_Syntax.ite_wp = uu____30761;
                             FStar_Syntax_Syntax.stronger = uu____30762;
                             FStar_Syntax_Syntax.close_wp = uu____30763;
                             FStar_Syntax_Syntax.assert_p = uu____30764;
                             FStar_Syntax_Syntax.assume_p = uu____30765;
                             FStar_Syntax_Syntax.null_wp = uu____30766;
                             FStar_Syntax_Syntax.trivial = uu____30767;
                             FStar_Syntax_Syntax.repr = uu____30768;
                             FStar_Syntax_Syntax.return_repr = uu____30769;
                             FStar_Syntax_Syntax.bind_repr = uu____30770;
                             FStar_Syntax_Syntax.actions = uu____30771;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___385_30757.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___386_30774 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___386_30774.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___386_30774.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___386_30774.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___386_30774.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___257_30795 =
            match uu___257_30795 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30826 = elim_uvars_aux_t env us [] t  in
                (match uu____30826 with
                 | (us1,uu____30854,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___387_30881 = sub_eff  in
            let uu____30882 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30885 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___387_30881.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___387_30881.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30882;
              FStar_Syntax_Syntax.lift = uu____30885
            }  in
          let uu___388_30888 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___388_30888.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___388_30888.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___388_30888.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___388_30888.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____30898 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30898 with
           | (univ_names1,binders1,comp1) ->
               let uu___389_30932 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___389_30932.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___389_30932.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___389_30932.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___389_30932.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30935 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30936 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  