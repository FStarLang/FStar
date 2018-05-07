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
      fun uu___101_269  ->
        match uu___101_269 with
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
      let add_opt x uu___102_1503 =
        match uu___102_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___120_1523 = fs  in
          {
            beta = true;
            iota = (uu___120_1523.iota);
            zeta = (uu___120_1523.zeta);
            weak = (uu___120_1523.weak);
            hnf = (uu___120_1523.hnf);
            primops = (uu___120_1523.primops);
            do_not_unfold_pure_lets = (uu___120_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1523.unfold_until);
            unfold_only = (uu___120_1523.unfold_only);
            unfold_fully = (uu___120_1523.unfold_fully);
            unfold_attr = (uu___120_1523.unfold_attr);
            unfold_tac = (uu___120_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1523.pure_subterms_within_computations);
            simplify = (uu___120_1523.simplify);
            erase_universes = (uu___120_1523.erase_universes);
            allow_unbound_universes = (uu___120_1523.allow_unbound_universes);
            reify_ = (uu___120_1523.reify_);
            compress_uvars = (uu___120_1523.compress_uvars);
            no_full_norm = (uu___120_1523.no_full_norm);
            check_no_uvars = (uu___120_1523.check_no_uvars);
            unmeta = (uu___120_1523.unmeta);
            unascribe = (uu___120_1523.unascribe);
            in_full_norm_request = (uu___120_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___121_1524 = fs  in
          {
            beta = (uu___121_1524.beta);
            iota = true;
            zeta = (uu___121_1524.zeta);
            weak = (uu___121_1524.weak);
            hnf = (uu___121_1524.hnf);
            primops = (uu___121_1524.primops);
            do_not_unfold_pure_lets = (uu___121_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___121_1524.unfold_until);
            unfold_only = (uu___121_1524.unfold_only);
            unfold_fully = (uu___121_1524.unfold_fully);
            unfold_attr = (uu___121_1524.unfold_attr);
            unfold_tac = (uu___121_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___121_1524.pure_subterms_within_computations);
            simplify = (uu___121_1524.simplify);
            erase_universes = (uu___121_1524.erase_universes);
            allow_unbound_universes = (uu___121_1524.allow_unbound_universes);
            reify_ = (uu___121_1524.reify_);
            compress_uvars = (uu___121_1524.compress_uvars);
            no_full_norm = (uu___121_1524.no_full_norm);
            check_no_uvars = (uu___121_1524.check_no_uvars);
            unmeta = (uu___121_1524.unmeta);
            unascribe = (uu___121_1524.unascribe);
            in_full_norm_request = (uu___121_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___121_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___122_1525 = fs  in
          {
            beta = (uu___122_1525.beta);
            iota = (uu___122_1525.iota);
            zeta = true;
            weak = (uu___122_1525.weak);
            hnf = (uu___122_1525.hnf);
            primops = (uu___122_1525.primops);
            do_not_unfold_pure_lets = (uu___122_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___122_1525.unfold_until);
            unfold_only = (uu___122_1525.unfold_only);
            unfold_fully = (uu___122_1525.unfold_fully);
            unfold_attr = (uu___122_1525.unfold_attr);
            unfold_tac = (uu___122_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___122_1525.pure_subterms_within_computations);
            simplify = (uu___122_1525.simplify);
            erase_universes = (uu___122_1525.erase_universes);
            allow_unbound_universes = (uu___122_1525.allow_unbound_universes);
            reify_ = (uu___122_1525.reify_);
            compress_uvars = (uu___122_1525.compress_uvars);
            no_full_norm = (uu___122_1525.no_full_norm);
            check_no_uvars = (uu___122_1525.check_no_uvars);
            unmeta = (uu___122_1525.unmeta);
            unascribe = (uu___122_1525.unascribe);
            in_full_norm_request = (uu___122_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___122_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___123_1526 = fs  in
          {
            beta = false;
            iota = (uu___123_1526.iota);
            zeta = (uu___123_1526.zeta);
            weak = (uu___123_1526.weak);
            hnf = (uu___123_1526.hnf);
            primops = (uu___123_1526.primops);
            do_not_unfold_pure_lets = (uu___123_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___123_1526.unfold_until);
            unfold_only = (uu___123_1526.unfold_only);
            unfold_fully = (uu___123_1526.unfold_fully);
            unfold_attr = (uu___123_1526.unfold_attr);
            unfold_tac = (uu___123_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_1526.pure_subterms_within_computations);
            simplify = (uu___123_1526.simplify);
            erase_universes = (uu___123_1526.erase_universes);
            allow_unbound_universes = (uu___123_1526.allow_unbound_universes);
            reify_ = (uu___123_1526.reify_);
            compress_uvars = (uu___123_1526.compress_uvars);
            no_full_norm = (uu___123_1526.no_full_norm);
            check_no_uvars = (uu___123_1526.check_no_uvars);
            unmeta = (uu___123_1526.unmeta);
            unascribe = (uu___123_1526.unascribe);
            in_full_norm_request = (uu___123_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___124_1527 = fs  in
          {
            beta = (uu___124_1527.beta);
            iota = false;
            zeta = (uu___124_1527.zeta);
            weak = (uu___124_1527.weak);
            hnf = (uu___124_1527.hnf);
            primops = (uu___124_1527.primops);
            do_not_unfold_pure_lets = (uu___124_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___124_1527.unfold_until);
            unfold_only = (uu___124_1527.unfold_only);
            unfold_fully = (uu___124_1527.unfold_fully);
            unfold_attr = (uu___124_1527.unfold_attr);
            unfold_tac = (uu___124_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___124_1527.pure_subterms_within_computations);
            simplify = (uu___124_1527.simplify);
            erase_universes = (uu___124_1527.erase_universes);
            allow_unbound_universes = (uu___124_1527.allow_unbound_universes);
            reify_ = (uu___124_1527.reify_);
            compress_uvars = (uu___124_1527.compress_uvars);
            no_full_norm = (uu___124_1527.no_full_norm);
            check_no_uvars = (uu___124_1527.check_no_uvars);
            unmeta = (uu___124_1527.unmeta);
            unascribe = (uu___124_1527.unascribe);
            in_full_norm_request = (uu___124_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___124_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___125_1528 = fs  in
          {
            beta = (uu___125_1528.beta);
            iota = (uu___125_1528.iota);
            zeta = false;
            weak = (uu___125_1528.weak);
            hnf = (uu___125_1528.hnf);
            primops = (uu___125_1528.primops);
            do_not_unfold_pure_lets = (uu___125_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___125_1528.unfold_until);
            unfold_only = (uu___125_1528.unfold_only);
            unfold_fully = (uu___125_1528.unfold_fully);
            unfold_attr = (uu___125_1528.unfold_attr);
            unfold_tac = (uu___125_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___125_1528.pure_subterms_within_computations);
            simplify = (uu___125_1528.simplify);
            erase_universes = (uu___125_1528.erase_universes);
            allow_unbound_universes = (uu___125_1528.allow_unbound_universes);
            reify_ = (uu___125_1528.reify_);
            compress_uvars = (uu___125_1528.compress_uvars);
            no_full_norm = (uu___125_1528.no_full_norm);
            check_no_uvars = (uu___125_1528.check_no_uvars);
            unmeta = (uu___125_1528.unmeta);
            unascribe = (uu___125_1528.unascribe);
            in_full_norm_request = (uu___125_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___125_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___126_1530 = fs  in
          {
            beta = (uu___126_1530.beta);
            iota = (uu___126_1530.iota);
            zeta = (uu___126_1530.zeta);
            weak = true;
            hnf = (uu___126_1530.hnf);
            primops = (uu___126_1530.primops);
            do_not_unfold_pure_lets = (uu___126_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1530.unfold_until);
            unfold_only = (uu___126_1530.unfold_only);
            unfold_fully = (uu___126_1530.unfold_fully);
            unfold_attr = (uu___126_1530.unfold_attr);
            unfold_tac = (uu___126_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1530.pure_subterms_within_computations);
            simplify = (uu___126_1530.simplify);
            erase_universes = (uu___126_1530.erase_universes);
            allow_unbound_universes = (uu___126_1530.allow_unbound_universes);
            reify_ = (uu___126_1530.reify_);
            compress_uvars = (uu___126_1530.compress_uvars);
            no_full_norm = (uu___126_1530.no_full_norm);
            check_no_uvars = (uu___126_1530.check_no_uvars);
            unmeta = (uu___126_1530.unmeta);
            unascribe = (uu___126_1530.unascribe);
            in_full_norm_request = (uu___126_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___127_1531 = fs  in
          {
            beta = (uu___127_1531.beta);
            iota = (uu___127_1531.iota);
            zeta = (uu___127_1531.zeta);
            weak = (uu___127_1531.weak);
            hnf = true;
            primops = (uu___127_1531.primops);
            do_not_unfold_pure_lets = (uu___127_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___127_1531.unfold_until);
            unfold_only = (uu___127_1531.unfold_only);
            unfold_fully = (uu___127_1531.unfold_fully);
            unfold_attr = (uu___127_1531.unfold_attr);
            unfold_tac = (uu___127_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___127_1531.pure_subterms_within_computations);
            simplify = (uu___127_1531.simplify);
            erase_universes = (uu___127_1531.erase_universes);
            allow_unbound_universes = (uu___127_1531.allow_unbound_universes);
            reify_ = (uu___127_1531.reify_);
            compress_uvars = (uu___127_1531.compress_uvars);
            no_full_norm = (uu___127_1531.no_full_norm);
            check_no_uvars = (uu___127_1531.check_no_uvars);
            unmeta = (uu___127_1531.unmeta);
            unascribe = (uu___127_1531.unascribe);
            in_full_norm_request = (uu___127_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___127_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___128_1532 = fs  in
          {
            beta = (uu___128_1532.beta);
            iota = (uu___128_1532.iota);
            zeta = (uu___128_1532.zeta);
            weak = (uu___128_1532.weak);
            hnf = (uu___128_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___128_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___128_1532.unfold_until);
            unfold_only = (uu___128_1532.unfold_only);
            unfold_fully = (uu___128_1532.unfold_fully);
            unfold_attr = (uu___128_1532.unfold_attr);
            unfold_tac = (uu___128_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_1532.pure_subterms_within_computations);
            simplify = (uu___128_1532.simplify);
            erase_universes = (uu___128_1532.erase_universes);
            allow_unbound_universes = (uu___128_1532.allow_unbound_universes);
            reify_ = (uu___128_1532.reify_);
            compress_uvars = (uu___128_1532.compress_uvars);
            no_full_norm = (uu___128_1532.no_full_norm);
            check_no_uvars = (uu___128_1532.check_no_uvars);
            unmeta = (uu___128_1532.unmeta);
            unascribe = (uu___128_1532.unascribe);
            in_full_norm_request = (uu___128_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___129_1533 = fs  in
          {
            beta = (uu___129_1533.beta);
            iota = (uu___129_1533.iota);
            zeta = (uu___129_1533.zeta);
            weak = (uu___129_1533.weak);
            hnf = (uu___129_1533.hnf);
            primops = (uu___129_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___129_1533.unfold_until);
            unfold_only = (uu___129_1533.unfold_only);
            unfold_fully = (uu___129_1533.unfold_fully);
            unfold_attr = (uu___129_1533.unfold_attr);
            unfold_tac = (uu___129_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1533.pure_subterms_within_computations);
            simplify = (uu___129_1533.simplify);
            erase_universes = (uu___129_1533.erase_universes);
            allow_unbound_universes = (uu___129_1533.allow_unbound_universes);
            reify_ = (uu___129_1533.reify_);
            compress_uvars = (uu___129_1533.compress_uvars);
            no_full_norm = (uu___129_1533.no_full_norm);
            check_no_uvars = (uu___129_1533.check_no_uvars);
            unmeta = (uu___129_1533.unmeta);
            unascribe = (uu___129_1533.unascribe);
            in_full_norm_request = (uu___129_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___130_1535 = fs  in
          {
            beta = (uu___130_1535.beta);
            iota = (uu___130_1535.iota);
            zeta = (uu___130_1535.zeta);
            weak = (uu___130_1535.weak);
            hnf = (uu___130_1535.hnf);
            primops = (uu___130_1535.primops);
            do_not_unfold_pure_lets = (uu___130_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___130_1535.unfold_only);
            unfold_fully = (uu___130_1535.unfold_fully);
            unfold_attr = (uu___130_1535.unfold_attr);
            unfold_tac = (uu___130_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___130_1535.pure_subterms_within_computations);
            simplify = (uu___130_1535.simplify);
            erase_universes = (uu___130_1535.erase_universes);
            allow_unbound_universes = (uu___130_1535.allow_unbound_universes);
            reify_ = (uu___130_1535.reify_);
            compress_uvars = (uu___130_1535.compress_uvars);
            no_full_norm = (uu___130_1535.no_full_norm);
            check_no_uvars = (uu___130_1535.check_no_uvars);
            unmeta = (uu___130_1535.unmeta);
            unascribe = (uu___130_1535.unascribe);
            in_full_norm_request = (uu___130_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___130_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___131_1539 = fs  in
          {
            beta = (uu___131_1539.beta);
            iota = (uu___131_1539.iota);
            zeta = (uu___131_1539.zeta);
            weak = (uu___131_1539.weak);
            hnf = (uu___131_1539.hnf);
            primops = (uu___131_1539.primops);
            do_not_unfold_pure_lets = (uu___131_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___131_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___131_1539.unfold_fully);
            unfold_attr = (uu___131_1539.unfold_attr);
            unfold_tac = (uu___131_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_1539.pure_subterms_within_computations);
            simplify = (uu___131_1539.simplify);
            erase_universes = (uu___131_1539.erase_universes);
            allow_unbound_universes = (uu___131_1539.allow_unbound_universes);
            reify_ = (uu___131_1539.reify_);
            compress_uvars = (uu___131_1539.compress_uvars);
            no_full_norm = (uu___131_1539.no_full_norm);
            check_no_uvars = (uu___131_1539.check_no_uvars);
            unmeta = (uu___131_1539.unmeta);
            unascribe = (uu___131_1539.unascribe);
            in_full_norm_request = (uu___131_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___132_1545 = fs  in
          {
            beta = (uu___132_1545.beta);
            iota = (uu___132_1545.iota);
            zeta = (uu___132_1545.zeta);
            weak = (uu___132_1545.weak);
            hnf = (uu___132_1545.hnf);
            primops = (uu___132_1545.primops);
            do_not_unfold_pure_lets = (uu___132_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___132_1545.unfold_until);
            unfold_only = (uu___132_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___132_1545.unfold_attr);
            unfold_tac = (uu___132_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_1545.pure_subterms_within_computations);
            simplify = (uu___132_1545.simplify);
            erase_universes = (uu___132_1545.erase_universes);
            allow_unbound_universes = (uu___132_1545.allow_unbound_universes);
            reify_ = (uu___132_1545.reify_);
            compress_uvars = (uu___132_1545.compress_uvars);
            no_full_norm = (uu___132_1545.no_full_norm);
            check_no_uvars = (uu___132_1545.check_no_uvars);
            unmeta = (uu___132_1545.unmeta);
            unascribe = (uu___132_1545.unascribe);
            in_full_norm_request = (uu___132_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___133_1549 = fs  in
          {
            beta = (uu___133_1549.beta);
            iota = (uu___133_1549.iota);
            zeta = (uu___133_1549.zeta);
            weak = (uu___133_1549.weak);
            hnf = (uu___133_1549.hnf);
            primops = (uu___133_1549.primops);
            do_not_unfold_pure_lets = (uu___133_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___133_1549.unfold_until);
            unfold_only = (uu___133_1549.unfold_only);
            unfold_fully = (uu___133_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___133_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_1549.pure_subterms_within_computations);
            simplify = (uu___133_1549.simplify);
            erase_universes = (uu___133_1549.erase_universes);
            allow_unbound_universes = (uu___133_1549.allow_unbound_universes);
            reify_ = (uu___133_1549.reify_);
            compress_uvars = (uu___133_1549.compress_uvars);
            no_full_norm = (uu___133_1549.no_full_norm);
            check_no_uvars = (uu___133_1549.check_no_uvars);
            unmeta = (uu___133_1549.unmeta);
            unascribe = (uu___133_1549.unascribe);
            in_full_norm_request = (uu___133_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___134_1550 = fs  in
          {
            beta = (uu___134_1550.beta);
            iota = (uu___134_1550.iota);
            zeta = (uu___134_1550.zeta);
            weak = (uu___134_1550.weak);
            hnf = (uu___134_1550.hnf);
            primops = (uu___134_1550.primops);
            do_not_unfold_pure_lets = (uu___134_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___134_1550.unfold_until);
            unfold_only = (uu___134_1550.unfold_only);
            unfold_fully = (uu___134_1550.unfold_fully);
            unfold_attr = (uu___134_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___134_1550.pure_subterms_within_computations);
            simplify = (uu___134_1550.simplify);
            erase_universes = (uu___134_1550.erase_universes);
            allow_unbound_universes = (uu___134_1550.allow_unbound_universes);
            reify_ = (uu___134_1550.reify_);
            compress_uvars = (uu___134_1550.compress_uvars);
            no_full_norm = (uu___134_1550.no_full_norm);
            check_no_uvars = (uu___134_1550.check_no_uvars);
            unmeta = (uu___134_1550.unmeta);
            unascribe = (uu___134_1550.unascribe);
            in_full_norm_request = (uu___134_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___135_1551 = fs  in
          {
            beta = (uu___135_1551.beta);
            iota = (uu___135_1551.iota);
            zeta = (uu___135_1551.zeta);
            weak = (uu___135_1551.weak);
            hnf = (uu___135_1551.hnf);
            primops = (uu___135_1551.primops);
            do_not_unfold_pure_lets = (uu___135_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___135_1551.unfold_until);
            unfold_only = (uu___135_1551.unfold_only);
            unfold_fully = (uu___135_1551.unfold_fully);
            unfold_attr = (uu___135_1551.unfold_attr);
            unfold_tac = (uu___135_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___135_1551.simplify);
            erase_universes = (uu___135_1551.erase_universes);
            allow_unbound_universes = (uu___135_1551.allow_unbound_universes);
            reify_ = (uu___135_1551.reify_);
            compress_uvars = (uu___135_1551.compress_uvars);
            no_full_norm = (uu___135_1551.no_full_norm);
            check_no_uvars = (uu___135_1551.check_no_uvars);
            unmeta = (uu___135_1551.unmeta);
            unascribe = (uu___135_1551.unascribe);
            in_full_norm_request = (uu___135_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___135_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___136_1552 = fs  in
          {
            beta = (uu___136_1552.beta);
            iota = (uu___136_1552.iota);
            zeta = (uu___136_1552.zeta);
            weak = (uu___136_1552.weak);
            hnf = (uu___136_1552.hnf);
            primops = (uu___136_1552.primops);
            do_not_unfold_pure_lets = (uu___136_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___136_1552.unfold_until);
            unfold_only = (uu___136_1552.unfold_only);
            unfold_fully = (uu___136_1552.unfold_fully);
            unfold_attr = (uu___136_1552.unfold_attr);
            unfold_tac = (uu___136_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___136_1552.erase_universes);
            allow_unbound_universes = (uu___136_1552.allow_unbound_universes);
            reify_ = (uu___136_1552.reify_);
            compress_uvars = (uu___136_1552.compress_uvars);
            no_full_norm = (uu___136_1552.no_full_norm);
            check_no_uvars = (uu___136_1552.check_no_uvars);
            unmeta = (uu___136_1552.unmeta);
            unascribe = (uu___136_1552.unascribe);
            in_full_norm_request = (uu___136_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___137_1553 = fs  in
          {
            beta = (uu___137_1553.beta);
            iota = (uu___137_1553.iota);
            zeta = (uu___137_1553.zeta);
            weak = (uu___137_1553.weak);
            hnf = (uu___137_1553.hnf);
            primops = (uu___137_1553.primops);
            do_not_unfold_pure_lets = (uu___137_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___137_1553.unfold_until);
            unfold_only = (uu___137_1553.unfold_only);
            unfold_fully = (uu___137_1553.unfold_fully);
            unfold_attr = (uu___137_1553.unfold_attr);
            unfold_tac = (uu___137_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_1553.pure_subterms_within_computations);
            simplify = (uu___137_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___137_1553.allow_unbound_universes);
            reify_ = (uu___137_1553.reify_);
            compress_uvars = (uu___137_1553.compress_uvars);
            no_full_norm = (uu___137_1553.no_full_norm);
            check_no_uvars = (uu___137_1553.check_no_uvars);
            unmeta = (uu___137_1553.unmeta);
            unascribe = (uu___137_1553.unascribe);
            in_full_norm_request = (uu___137_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___138_1554 = fs  in
          {
            beta = (uu___138_1554.beta);
            iota = (uu___138_1554.iota);
            zeta = (uu___138_1554.zeta);
            weak = (uu___138_1554.weak);
            hnf = (uu___138_1554.hnf);
            primops = (uu___138_1554.primops);
            do_not_unfold_pure_lets = (uu___138_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___138_1554.unfold_until);
            unfold_only = (uu___138_1554.unfold_only);
            unfold_fully = (uu___138_1554.unfold_fully);
            unfold_attr = (uu___138_1554.unfold_attr);
            unfold_tac = (uu___138_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_1554.pure_subterms_within_computations);
            simplify = (uu___138_1554.simplify);
            erase_universes = (uu___138_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___138_1554.reify_);
            compress_uvars = (uu___138_1554.compress_uvars);
            no_full_norm = (uu___138_1554.no_full_norm);
            check_no_uvars = (uu___138_1554.check_no_uvars);
            unmeta = (uu___138_1554.unmeta);
            unascribe = (uu___138_1554.unascribe);
            in_full_norm_request = (uu___138_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___139_1555 = fs  in
          {
            beta = (uu___139_1555.beta);
            iota = (uu___139_1555.iota);
            zeta = (uu___139_1555.zeta);
            weak = (uu___139_1555.weak);
            hnf = (uu___139_1555.hnf);
            primops = (uu___139_1555.primops);
            do_not_unfold_pure_lets = (uu___139_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___139_1555.unfold_until);
            unfold_only = (uu___139_1555.unfold_only);
            unfold_fully = (uu___139_1555.unfold_fully);
            unfold_attr = (uu___139_1555.unfold_attr);
            unfold_tac = (uu___139_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___139_1555.pure_subterms_within_computations);
            simplify = (uu___139_1555.simplify);
            erase_universes = (uu___139_1555.erase_universes);
            allow_unbound_universes = (uu___139_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___139_1555.compress_uvars);
            no_full_norm = (uu___139_1555.no_full_norm);
            check_no_uvars = (uu___139_1555.check_no_uvars);
            unmeta = (uu___139_1555.unmeta);
            unascribe = (uu___139_1555.unascribe);
            in_full_norm_request = (uu___139_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___139_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___140_1556 = fs  in
          {
            beta = (uu___140_1556.beta);
            iota = (uu___140_1556.iota);
            zeta = (uu___140_1556.zeta);
            weak = (uu___140_1556.weak);
            hnf = (uu___140_1556.hnf);
            primops = (uu___140_1556.primops);
            do_not_unfold_pure_lets = (uu___140_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___140_1556.unfold_until);
            unfold_only = (uu___140_1556.unfold_only);
            unfold_fully = (uu___140_1556.unfold_fully);
            unfold_attr = (uu___140_1556.unfold_attr);
            unfold_tac = (uu___140_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___140_1556.pure_subterms_within_computations);
            simplify = (uu___140_1556.simplify);
            erase_universes = (uu___140_1556.erase_universes);
            allow_unbound_universes = (uu___140_1556.allow_unbound_universes);
            reify_ = (uu___140_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___140_1556.no_full_norm);
            check_no_uvars = (uu___140_1556.check_no_uvars);
            unmeta = (uu___140_1556.unmeta);
            unascribe = (uu___140_1556.unascribe);
            in_full_norm_request = (uu___140_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___141_1557 = fs  in
          {
            beta = (uu___141_1557.beta);
            iota = (uu___141_1557.iota);
            zeta = (uu___141_1557.zeta);
            weak = (uu___141_1557.weak);
            hnf = (uu___141_1557.hnf);
            primops = (uu___141_1557.primops);
            do_not_unfold_pure_lets = (uu___141_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___141_1557.unfold_until);
            unfold_only = (uu___141_1557.unfold_only);
            unfold_fully = (uu___141_1557.unfold_fully);
            unfold_attr = (uu___141_1557.unfold_attr);
            unfold_tac = (uu___141_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___141_1557.pure_subterms_within_computations);
            simplify = (uu___141_1557.simplify);
            erase_universes = (uu___141_1557.erase_universes);
            allow_unbound_universes = (uu___141_1557.allow_unbound_universes);
            reify_ = (uu___141_1557.reify_);
            compress_uvars = (uu___141_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___141_1557.check_no_uvars);
            unmeta = (uu___141_1557.unmeta);
            unascribe = (uu___141_1557.unascribe);
            in_full_norm_request = (uu___141_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___142_1558 = fs  in
          {
            beta = (uu___142_1558.beta);
            iota = (uu___142_1558.iota);
            zeta = (uu___142_1558.zeta);
            weak = (uu___142_1558.weak);
            hnf = (uu___142_1558.hnf);
            primops = (uu___142_1558.primops);
            do_not_unfold_pure_lets = (uu___142_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1558.unfold_until);
            unfold_only = (uu___142_1558.unfold_only);
            unfold_fully = (uu___142_1558.unfold_fully);
            unfold_attr = (uu___142_1558.unfold_attr);
            unfold_tac = (uu___142_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1558.pure_subterms_within_computations);
            simplify = (uu___142_1558.simplify);
            erase_universes = (uu___142_1558.erase_universes);
            allow_unbound_universes = (uu___142_1558.allow_unbound_universes);
            reify_ = (uu___142_1558.reify_);
            compress_uvars = (uu___142_1558.compress_uvars);
            no_full_norm = (uu___142_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___142_1558.unmeta);
            unascribe = (uu___142_1558.unascribe);
            in_full_norm_request = (uu___142_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___143_1559 = fs  in
          {
            beta = (uu___143_1559.beta);
            iota = (uu___143_1559.iota);
            zeta = (uu___143_1559.zeta);
            weak = (uu___143_1559.weak);
            hnf = (uu___143_1559.hnf);
            primops = (uu___143_1559.primops);
            do_not_unfold_pure_lets = (uu___143_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___143_1559.unfold_until);
            unfold_only = (uu___143_1559.unfold_only);
            unfold_fully = (uu___143_1559.unfold_fully);
            unfold_attr = (uu___143_1559.unfold_attr);
            unfold_tac = (uu___143_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___143_1559.pure_subterms_within_computations);
            simplify = (uu___143_1559.simplify);
            erase_universes = (uu___143_1559.erase_universes);
            allow_unbound_universes = (uu___143_1559.allow_unbound_universes);
            reify_ = (uu___143_1559.reify_);
            compress_uvars = (uu___143_1559.compress_uvars);
            no_full_norm = (uu___143_1559.no_full_norm);
            check_no_uvars = (uu___143_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___143_1559.unascribe);
            in_full_norm_request = (uu___143_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___143_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___144_1560 = fs  in
          {
            beta = (uu___144_1560.beta);
            iota = (uu___144_1560.iota);
            zeta = (uu___144_1560.zeta);
            weak = (uu___144_1560.weak);
            hnf = (uu___144_1560.hnf);
            primops = (uu___144_1560.primops);
            do_not_unfold_pure_lets = (uu___144_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___144_1560.unfold_until);
            unfold_only = (uu___144_1560.unfold_only);
            unfold_fully = (uu___144_1560.unfold_fully);
            unfold_attr = (uu___144_1560.unfold_attr);
            unfold_tac = (uu___144_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_1560.pure_subterms_within_computations);
            simplify = (uu___144_1560.simplify);
            erase_universes = (uu___144_1560.erase_universes);
            allow_unbound_universes = (uu___144_1560.allow_unbound_universes);
            reify_ = (uu___144_1560.reify_);
            compress_uvars = (uu___144_1560.compress_uvars);
            no_full_norm = (uu___144_1560.no_full_norm);
            check_no_uvars = (uu___144_1560.check_no_uvars);
            unmeta = (uu___144_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___144_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_1560.weakly_reduce_scrutinee)
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
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }
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
             let uu____2351 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2351 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2365 = FStar_Util.psmap_empty ()  in add_steps uu____2365 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2380 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2380
  
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
    match projectee with | Arg _0 -> true | uu____2538 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2576 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2614 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2687 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2737 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2795 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2839 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2879 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2917 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2935 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2962 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2962 with | (hd1,uu____2976) -> hd1
  
let mk :
  'Auu____2999 .
    'Auu____2999 ->
      FStar_Range.range -> 'Auu____2999 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3062 = FStar_ST.op_Bang r  in
          match uu____3062 with
          | FStar_Pervasives_Native.Some uu____3114 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3190 =
      FStar_List.map
        (fun uu____3204  ->
           match uu____3204 with
           | (bopt,c) ->
               let uu____3217 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3219 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3217 uu____3219) env
       in
    FStar_All.pipe_right uu____3190 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___103_3222  ->
    match uu___103_3222 with
    | Clos (env,t,uu____3225,uu____3226) ->
        let uu____3271 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3278 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3271 uu____3278
    | Univ uu____3279 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___104_3284  ->
    match uu___104_3284 with
    | Arg (c,uu____3286,uu____3287) ->
        let uu____3288 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3288
    | MemoLazy uu____3289 -> "MemoLazy"
    | Abs (uu____3296,bs,uu____3298,uu____3299,uu____3300) ->
        let uu____3305 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3305
    | UnivArgs uu____3310 -> "UnivArgs"
    | Match uu____3317 -> "Match"
    | App (uu____3326,t,uu____3328,uu____3329) ->
        let uu____3330 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3330
    | Meta (uu____3331,m,uu____3333) -> "Meta"
    | Let uu____3334 -> "Let"
    | Cfg uu____3343 -> "Cfg"
    | Debug (t,uu____3345) ->
        let uu____3346 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3346
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3356 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3356 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3397 . 'Auu____3397 Prims.list -> Prims.bool =
  fun uu___105_3404  ->
    match uu___105_3404 with | [] -> true | uu____3407 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3439 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3439
      with
      | uu____3458 ->
          let uu____3459 =
            let uu____3460 = FStar_Syntax_Print.db_to_string x  in
            let uu____3461 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3460
              uu____3461
             in
          failwith uu____3459
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3469 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3469
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3473 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3473
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3477 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3477
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
          let uu____3511 =
            FStar_List.fold_left
              (fun uu____3537  ->
                 fun u1  ->
                   match uu____3537 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3562 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3562 with
                        | (k_u,n1) ->
                            let uu____3577 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3577
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3511 with
          | (uu____3595,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3622 =
                   let uu____3623 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3623  in
                 match uu____3622 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3641 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3649 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3655 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3664 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3673 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3680 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3680 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3697 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3697 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3705 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3713 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3713 with
                                  | (uu____3718,m) -> n1 <= m))
                           in
                        if uu____3705 then rest1 else us1
                    | uu____3723 -> us1)
               | uu____3728 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3732 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3732
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3736 = aux u  in
           match uu____3736 with
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
            (fun uu____3882  ->
               let uu____3883 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3884 = env_to_string env  in
               let uu____3885 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3883 uu____3884 uu____3885);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3894 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3897 ->
                    let uu____3922 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3922
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3923 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3924 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3925 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3926 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3927 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3949 ->
                           let uu____3966 =
                             let uu____3967 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3968 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3967 uu____3968
                              in
                           failwith uu____3966
                       | uu____3971 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3977 =
                        let uu____3978 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3978  in
                      mk uu____3977 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3986 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3986  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3988 = lookup_bvar env x  in
                    (match uu____3988 with
                     | Univ uu____3991 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___149_3995 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___149_3995.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___149_3995.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4001,uu____4002) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4087  ->
                              fun stack1  ->
                                match uu____4087 with
                                | (a,aq) ->
                                    let uu____4099 =
                                      let uu____4100 =
                                        let uu____4107 =
                                          let uu____4108 =
                                            let uu____4139 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4139, false)  in
                                          Clos uu____4108  in
                                        (uu____4107, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4100  in
                                    uu____4099 :: stack1) args)
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
                    let uu____4333 = close_binders cfg env bs  in
                    (match uu____4333 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4380 =
                      let uu____4391 =
                        let uu____4398 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4398]  in
                      close_binders cfg env uu____4391  in
                    (match uu____4380 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4421 =
                             let uu____4422 =
                               let uu____4429 =
                                 let uu____4430 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4430
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4429, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4422  in
                           mk uu____4421 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4521 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4521
                      | FStar_Util.Inr c ->
                          let uu____4535 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4535
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4554 =
                        let uu____4555 =
                          let uu____4582 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4582, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4555  in
                      mk uu____4554 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4628 =
                            let uu____4629 =
                              let uu____4636 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4636, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4629  in
                          mk uu____4628 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4688  -> dummy :: env1) env
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
                    let uu____4709 =
                      let uu____4720 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4720
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4739 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___150_4755 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___150_4755.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___150_4755.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4739))
                       in
                    (match uu____4709 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___151_4773 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___151_4773.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___151_4773.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___151_4773.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___151_4773.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4787,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4850  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4875 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4875
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4895  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4919 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4919
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___152_4927 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_4927.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_4927.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___153_4928 = lb  in
                      let uu____4929 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___153_4928.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___153_4928.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4929;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___153_4928.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___153_4928.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4961  -> fun env1  -> dummy :: env1)
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
            (fun uu____5064  ->
               let uu____5065 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5066 = env_to_string env  in
               let uu____5067 = stack_to_string stack  in
               let uu____5068 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5065 uu____5066 uu____5067 uu____5068);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5073,uu____5074),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5149 = close_binders cfg env' bs  in
               (match uu____5149 with
                | (bs1,uu____5163) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5179 =
                      let uu___154_5180 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___154_5180.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___154_5180.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5179)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5226 =
                 match uu____5226 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5301 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5322 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5382  ->
                                     fun uu____5383  ->
                                       match (uu____5382, uu____5383) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5474 = norm_pat env4 p1
                                              in
                                           (match uu____5474 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5322 with
                            | (pats1,env4) ->
                                ((let uu___155_5556 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___155_5556.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___156_5575 = x  in
                             let uu____5576 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___156_5575.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___156_5575.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5576
                             }  in
                           ((let uu___157_5590 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___157_5590.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___158_5601 = x  in
                             let uu____5602 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_5601.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_5601.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5602
                             }  in
                           ((let uu___159_5616 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___159_5616.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___160_5632 = x  in
                             let uu____5633 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_5632.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_5632.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5633
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___161_5642 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___161_5642.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5647 = norm_pat env2 pat  in
                     (match uu____5647 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5692 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5692
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5711 =
                   let uu____5712 =
                     let uu____5735 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5735)  in
                   FStar_Syntax_Syntax.Tm_match uu____5712  in
                 mk uu____5711 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5830 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5919  ->
                                       match uu____5919 with
                                       | (a,q) ->
                                           let uu____5938 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5938, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5830
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5949 =
                       let uu____5956 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5956)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5949
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5968 =
                       let uu____5977 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5977)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5968
                 | uu____5982 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5986 -> failwith "Impossible: unexpected stack element")

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
        let uu____6000 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6049  ->
                  fun uu____6050  ->
                    match (uu____6049, uu____6050) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___162_6120 = b  in
                          let uu____6121 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___162_6120.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___162_6120.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6121
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6000 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6214 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6227 = inline_closure_env cfg env [] t  in
                 let uu____6228 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6227 uu____6228
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6241 = inline_closure_env cfg env [] t  in
                 let uu____6242 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6241 uu____6242
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6288  ->
                           match uu____6288 with
                           | (a,q) ->
                               let uu____6301 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6301, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___106_6316  ->
                           match uu___106_6316 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6320 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6320
                           | f -> f))
                    in
                 let uu____6324 =
                   let uu___163_6325 = c1  in
                   let uu____6326 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6326;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___163_6325.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6324)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___107_6336  ->
            match uu___107_6336 with
            | FStar_Syntax_Syntax.DECREASES uu____6337 -> false
            | uu____6340 -> true))

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
                   (fun uu___108_6358  ->
                      match uu___108_6358 with
                      | FStar_Syntax_Syntax.DECREASES uu____6359 -> false
                      | uu____6362 -> true))
               in
            let rc1 =
              let uu___164_6364 = rc  in
              let uu____6365 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___164_6364.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6365;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6374 -> lopt

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
    let uu____6487 =
      let uu____6496 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6496  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6487  in
  let arg_as_bounded_int uu____6522 =
    match uu____6522 with
    | (a,uu____6534) ->
        let uu____6541 =
          let uu____6542 = FStar_Syntax_Subst.compress a  in
          uu____6542.FStar_Syntax_Syntax.n  in
        (match uu____6541 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6552;
                FStar_Syntax_Syntax.vars = uu____6553;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6555;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6556;_},uu____6557)::[])
             when
             let uu____6596 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6596 "int_to_t" ->
             let uu____6597 =
               let uu____6602 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6602)  in
             FStar_Pervasives_Native.Some uu____6597
         | uu____6607 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6655 = f a  in FStar_Pervasives_Native.Some uu____6655
    | uu____6656 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6712 = f a0 a1  in FStar_Pervasives_Native.Some uu____6712
    | uu____6713 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6771 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6771  in
  let binary_op as_a f res args =
    let uu____6836 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6836  in
  let as_primitive_step is_strong uu____6867 =
    match uu____6867 with
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
           let uu____6927 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6927)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6963 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6963)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____6992 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____6992)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7028 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7028)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7064 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7064)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7196 =
          let uu____7205 = as_a a  in
          let uu____7208 = as_b b  in (uu____7205, uu____7208)  in
        (match uu____7196 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7223 =
               let uu____7224 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7224  in
             FStar_Pervasives_Native.Some uu____7223
         | uu____7225 -> FStar_Pervasives_Native.None)
    | uu____7234 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7254 =
        let uu____7255 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7255  in
      mk uu____7254 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7267 =
      let uu____7270 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7270  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7267  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7312 =
      let uu____7313 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7313  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7312
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7335 = arg_as_string a1  in
        (match uu____7335 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7341 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7341 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7354 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7354
              | uu____7355 -> FStar_Pervasives_Native.None)
         | uu____7360 -> FStar_Pervasives_Native.None)
    | uu____7363 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7377 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7377
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7414 =
          let uu____7435 = arg_as_string fn  in
          let uu____7438 = arg_as_int from_line  in
          let uu____7441 = arg_as_int from_col  in
          let uu____7444 = arg_as_int to_line  in
          let uu____7447 = arg_as_int to_col  in
          (uu____7435, uu____7438, uu____7441, uu____7444, uu____7447)  in
        (match uu____7414 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7478 =
                 let uu____7479 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7480 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7479 uu____7480  in
               let uu____7481 =
                 let uu____7482 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7483 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7482 uu____7483  in
               FStar_Range.mk_range fn1 uu____7478 uu____7481  in
             let uu____7484 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7484
         | uu____7485 -> FStar_Pervasives_Native.None)
    | uu____7506 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7539)::(a1,uu____7541)::(a2,uu____7543)::[] ->
        let uu____7580 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7580 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7593 -> FStar_Pervasives_Native.None)
    | uu____7594 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7625)::[] ->
        let uu____7634 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7634 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7640 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7640
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7641 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7667 =
      let uu____7684 =
        let uu____7701 =
          let uu____7718 =
            let uu____7735 =
              let uu____7752 =
                let uu____7769 =
                  let uu____7786 =
                    let uu____7803 =
                      let uu____7820 =
                        let uu____7837 =
                          let uu____7854 =
                            let uu____7871 =
                              let uu____7888 =
                                let uu____7905 =
                                  let uu____7922 =
                                    let uu____7939 =
                                      let uu____7956 =
                                        let uu____7973 =
                                          let uu____7990 =
                                            let uu____8007 =
                                              let uu____8024 =
                                                let uu____8039 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8039,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8048 =
                                                let uu____8065 =
                                                  let uu____8080 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8080,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8093 =
                                                  let uu____8110 =
                                                    let uu____8127 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8127,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8138 =
                                                    let uu____8157 =
                                                      let uu____8174 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8174,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8157]  in
                                                  uu____8110 :: uu____8138
                                                   in
                                                uu____8065 :: uu____8093  in
                                              uu____8024 :: uu____8048  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8007
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7990
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7973
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7956
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7939
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8402 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8402 y)))
                                    :: uu____7922
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7905
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7888
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7871
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7854
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7837
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7820
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8597 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8597)))
                      :: uu____7803
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8627 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8627)))
                    :: uu____7786
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8657 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8657)))
                  :: uu____7769
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8687 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8687)))
                :: uu____7752
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7735
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7718
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7701
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7684
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7667
     in
  let weak_ops =
    let uu____8848 =
      let uu____8869 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8869, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8848]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8967 =
        let uu____8972 =
          let uu____8973 = FStar_Syntax_Syntax.as_arg c  in [uu____8973]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8972  in
      uu____8967 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9029 =
                let uu____9044 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9044, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9066  ->
                          fun uu____9067  ->
                            match (uu____9066, uu____9067) with
                            | ((int_to_t1,x),(uu____9086,y)) ->
                                let uu____9096 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9096)))
                 in
              let uu____9097 =
                let uu____9114 =
                  let uu____9129 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9129, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9151  ->
                            fun uu____9152  ->
                              match (uu____9151, uu____9152) with
                              | ((int_to_t1,x),(uu____9171,y)) ->
                                  let uu____9181 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9181)))
                   in
                let uu____9182 =
                  let uu____9199 =
                    let uu____9214 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9214, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9236  ->
                              fun uu____9237  ->
                                match (uu____9236, uu____9237) with
                                | ((int_to_t1,x),(uu____9256,y)) ->
                                    let uu____9266 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9266)))
                     in
                  let uu____9267 =
                    let uu____9284 =
                      let uu____9299 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9299, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9317  ->
                                match uu____9317 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9284]  in
                  uu____9199 :: uu____9267  in
                uu____9114 :: uu____9182  in
              uu____9029 :: uu____9097))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9447 =
                let uu____9462 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9462, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9484  ->
                          fun uu____9485  ->
                            match (uu____9484, uu____9485) with
                            | ((int_to_t1,x),(uu____9504,y)) ->
                                let uu____9514 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9514)))
                 in
              let uu____9515 =
                let uu____9532 =
                  let uu____9547 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9547, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9569  ->
                            fun uu____9570  ->
                              match (uu____9569, uu____9570) with
                              | ((int_to_t1,x),(uu____9589,y)) ->
                                  let uu____9599 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9599)))
                   in
                [uu____9532]  in
              uu____9447 :: uu____9515))
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
    | (_typ,uu____9729)::(a1,uu____9731)::(a2,uu____9733)::[] ->
        let uu____9770 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9770 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___165_9776 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_9776.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_9776.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___166_9780 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_9780.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_9780.FStar_Syntax_Syntax.vars)
                })
         | uu____9781 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9783)::uu____9784::(a1,uu____9786)::(a2,uu____9788)::[] ->
        let uu____9837 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9837 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___165_9843 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___165_9843.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___165_9843.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___166_9847 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___166_9847.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___166_9847.FStar_Syntax_Syntax.vars)
                })
         | uu____9848 -> FStar_Pervasives_Native.None)
    | uu____9849 -> failwith "Unexpected number of arguments"  in
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
    let uu____9903 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9903 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9955 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9955) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10017  ->
           fun subst1  ->
             match uu____10017 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10058,uu____10059)) ->
                      let uu____10118 = b  in
                      (match uu____10118 with
                       | (bv,uu____10126) ->
                           let uu____10127 =
                             let uu____10128 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10128  in
                           if uu____10127
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10133 = unembed_binder term1  in
                              match uu____10133 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10140 =
                                      let uu___167_10141 = bv  in
                                      let uu____10142 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___167_10141.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___167_10141.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10142
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10140
                                     in
                                  let b_for_x =
                                    let uu____10146 =
                                      let uu____10153 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10153)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10146  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___109_10163  ->
                                         match uu___109_10163 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10164,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10166;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10167;_})
                                             ->
                                             let uu____10172 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10172
                                         | uu____10173 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10174 -> subst1)) env []
  
let reduce_primops :
  'Auu____10197 'Auu____10198 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10197) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10198 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10244 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10244 with
             | (head1,args) ->
                 let uu____10281 =
                   let uu____10282 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10282.FStar_Syntax_Syntax.n  in
                 (match uu____10281 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10286 = find_prim_step cfg fv  in
                      (match uu____10286 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10308  ->
                                   let uu____10309 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10310 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10317 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10309 uu____10310 uu____10317);
                              tm)
                           else
                             (let uu____10319 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10319 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10430  ->
                                        let uu____10431 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10431);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10434  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10436 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10436 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10442  ->
                                              let uu____10443 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10443);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10449  ->
                                              let uu____10450 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10451 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10450 uu____10451);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10452 ->
                           (log_primops cfg
                              (fun uu____10456  ->
                                 let uu____10457 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10457);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10461  ->
                            let uu____10462 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10462);
                       (match args with
                        | (a1,uu____10464)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10481 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10493  ->
                            let uu____10494 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10494);
                       (match args with
                        | (t,uu____10496)::(r,uu____10498)::[] ->
                            let uu____10525 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10525 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10529 -> tm))
                  | uu____10538 -> tm))
  
let reduce_equality :
  'Auu____10549 'Auu____10550 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10549) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10550 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___168_10594 = cfg  in
         {
           steps =
             (let uu___169_10597 = default_steps  in
              {
                beta = (uu___169_10597.beta);
                iota = (uu___169_10597.iota);
                zeta = (uu___169_10597.zeta);
                weak = (uu___169_10597.weak);
                hnf = (uu___169_10597.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___169_10597.do_not_unfold_pure_lets);
                unfold_until = (uu___169_10597.unfold_until);
                unfold_only = (uu___169_10597.unfold_only);
                unfold_fully = (uu___169_10597.unfold_fully);
                unfold_attr = (uu___169_10597.unfold_attr);
                unfold_tac = (uu___169_10597.unfold_tac);
                pure_subterms_within_computations =
                  (uu___169_10597.pure_subterms_within_computations);
                simplify = (uu___169_10597.simplify);
                erase_universes = (uu___169_10597.erase_universes);
                allow_unbound_universes =
                  (uu___169_10597.allow_unbound_universes);
                reify_ = (uu___169_10597.reify_);
                compress_uvars = (uu___169_10597.compress_uvars);
                no_full_norm = (uu___169_10597.no_full_norm);
                check_no_uvars = (uu___169_10597.check_no_uvars);
                unmeta = (uu___169_10597.unmeta);
                unascribe = (uu___169_10597.unascribe);
                in_full_norm_request = (uu___169_10597.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___169_10597.weakly_reduce_scrutinee)
              });
           tcenv = (uu___168_10594.tcenv);
           debug = (uu___168_10594.debug);
           delta_level = (uu___168_10594.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___168_10594.strong);
           memoize_lazy = (uu___168_10594.memoize_lazy);
           normalize_pure_lets = (uu___168_10594.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10604 .
    FStar_Syntax_Syntax.term -> 'Auu____10604 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10619 =
        let uu____10626 =
          let uu____10627 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10627.FStar_Syntax_Syntax.n  in
        (uu____10626, args)  in
      match uu____10619 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10633::uu____10634::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10638::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10643::uu____10644::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10647 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___110_10660  ->
    match uu___110_10660 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10666 =
          let uu____10669 =
            let uu____10670 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10670  in
          [uu____10669]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10666
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10676 =
          let uu____10679 =
            let uu____10680 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10680  in
          [uu____10679]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10676
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10701 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10701) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10747 =
          let uu____10752 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10752 s  in
        match uu____10747 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10768 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10768
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10785::(tm,uu____10787)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10816)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10837)::uu____10838::(tm,uu____10840)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10881 =
            let uu____10886 = full_norm steps  in parse_steps uu____10886  in
          (match uu____10881 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10925 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___111_10944  ->
    match uu___111_10944 with
    | (App
        (uu____10947,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10948;
                       FStar_Syntax_Syntax.vars = uu____10949;_},uu____10950,uu____10951))::uu____10952
        -> true
    | uu____10959 -> false
  
let firstn :
  'Auu____10968 .
    Prims.int ->
      'Auu____10968 Prims.list ->
        ('Auu____10968 Prims.list,'Auu____10968 Prims.list)
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
          (uu____11010,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11011;
                         FStar_Syntax_Syntax.vars = uu____11012;_},uu____11013,uu____11014))::uu____11015
          -> (cfg.steps).reify_
      | uu____11022 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11045) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11055) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11074  ->
                  match uu____11074 with
                  | (a,uu____11082) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11088 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11113 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11114 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11131 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11132 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11133 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11134 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11135 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11136 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11143 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11150 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11163 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11180 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11193 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11200 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11262  ->
                   match uu____11262 with
                   | (a,uu____11270) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11277) ->
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
                     (fun uu____11399  ->
                        match uu____11399 with
                        | (a,uu____11407) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11412,uu____11413,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11419,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11425 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11432 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11433 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11725 ->
                   let uu____11750 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11750
               | uu____11751 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11759  ->
               let uu____11760 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11761 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11762 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11769 =
                 let uu____11770 =
                   let uu____11773 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11773
                    in
                 stack_to_string uu____11770  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11760 uu____11761 uu____11762 uu____11769);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11796 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11797 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11798 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11799;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____11800;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11803;
                 FStar_Syntax_Syntax.fv_delta = uu____11804;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11805;
                 FStar_Syntax_Syntax.fv_delta = uu____11806;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11807);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11814 ->
               let uu____11821 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11821
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11851 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11851)
               ->
               let cfg' =
                 let uu___170_11853 = cfg  in
                 {
                   steps =
                     (let uu___171_11856 = cfg.steps  in
                      {
                        beta = (uu___171_11856.beta);
                        iota = (uu___171_11856.iota);
                        zeta = (uu___171_11856.zeta);
                        weak = (uu___171_11856.weak);
                        hnf = (uu___171_11856.hnf);
                        primops = (uu___171_11856.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___171_11856.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___171_11856.unfold_attr);
                        unfold_tac = (uu___171_11856.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___171_11856.pure_subterms_within_computations);
                        simplify = (uu___171_11856.simplify);
                        erase_universes = (uu___171_11856.erase_universes);
                        allow_unbound_universes =
                          (uu___171_11856.allow_unbound_universes);
                        reify_ = (uu___171_11856.reify_);
                        compress_uvars = (uu___171_11856.compress_uvars);
                        no_full_norm = (uu___171_11856.no_full_norm);
                        check_no_uvars = (uu___171_11856.check_no_uvars);
                        unmeta = (uu___171_11856.unmeta);
                        unascribe = (uu___171_11856.unascribe);
                        in_full_norm_request =
                          (uu___171_11856.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___171_11856.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___170_11853.tcenv);
                   debug = (uu___170_11853.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___170_11853.primitive_steps);
                   strong = (uu___170_11853.strong);
                   memoize_lazy = (uu___170_11853.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11861 = get_norm_request (norm cfg' env []) args  in
               (match uu____11861 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11892  ->
                              fun stack1  ->
                                match uu____11892 with
                                | (a,aq) ->
                                    let uu____11904 =
                                      let uu____11905 =
                                        let uu____11912 =
                                          let uu____11913 =
                                            let uu____11944 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11944, false)  in
                                          Clos uu____11913  in
                                        (uu____11912, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11905  in
                                    uu____11904 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12028  ->
                          let uu____12029 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12029);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12051 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___112_12056  ->
                                match uu___112_12056 with
                                | UnfoldUntil uu____12057 -> true
                                | UnfoldOnly uu____12058 -> true
                                | UnfoldFully uu____12061 -> true
                                | uu____12064 -> false))
                         in
                      if uu____12051
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___172_12069 = cfg  in
                      let uu____12070 =
                        let uu___173_12071 = to_fsteps s  in
                        {
                          beta = (uu___173_12071.beta);
                          iota = (uu___173_12071.iota);
                          zeta = (uu___173_12071.zeta);
                          weak = (uu___173_12071.weak);
                          hnf = (uu___173_12071.hnf);
                          primops = (uu___173_12071.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_12071.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_12071.unfold_until);
                          unfold_only = (uu___173_12071.unfold_only);
                          unfold_fully = (uu___173_12071.unfold_fully);
                          unfold_attr = (uu___173_12071.unfold_attr);
                          unfold_tac = (uu___173_12071.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_12071.pure_subterms_within_computations);
                          simplify = (uu___173_12071.simplify);
                          erase_universes = (uu___173_12071.erase_universes);
                          allow_unbound_universes =
                            (uu___173_12071.allow_unbound_universes);
                          reify_ = (uu___173_12071.reify_);
                          compress_uvars = (uu___173_12071.compress_uvars);
                          no_full_norm = (uu___173_12071.no_full_norm);
                          check_no_uvars = (uu___173_12071.check_no_uvars);
                          unmeta = (uu___173_12071.unmeta);
                          unascribe = (uu___173_12071.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___173_12071.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12070;
                        tcenv = (uu___172_12069.tcenv);
                        debug = (uu___172_12069.debug);
                        delta_level;
                        primitive_steps = (uu___172_12069.primitive_steps);
                        strong = (uu___172_12069.strong);
                        memoize_lazy = (uu___172_12069.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12080 =
                          let uu____12081 =
                            let uu____12086 = FStar_Util.now ()  in
                            (t1, uu____12086)  in
                          Debug uu____12081  in
                        uu____12080 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12090 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12090
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12099 =
                      let uu____12106 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12106, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12099  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12116 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12116  in
               let uu____12117 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12117
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12123  ->
                       let uu____12124 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12125 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12124 uu____12125);
                  if b
                  then
                    (let uu____12126 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12126 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12134 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12134) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12147),uu____12148);
                                FStar_Syntax_Syntax.sigrng = uu____12149;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12151;
                                FStar_Syntax_Syntax.sigattrs = uu____12152;_},uu____12153),uu____12154)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12219 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___113_12223  ->
                               match uu___113_12223 with
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
                          (let uu____12233 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12233))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12252) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12287,uu____12288) -> false)))
                     in
                  let uu____12305 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12321 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12321 then (true, true) else (false, false)
                     in
                  match uu____12305 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12334  ->
                            let uu____12335 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12336 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12337 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12335 uu____12336 uu____12337);
                       if should_delta2
                       then
                         (let uu____12338 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___174_12354 = cfg  in
                                 {
                                   steps =
                                     (let uu___175_12357 = cfg.steps  in
                                      {
                                        beta = (uu___175_12357.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___175_12357.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___175_12357.unfold_attr);
                                        unfold_tac =
                                          (uu___175_12357.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___175_12357.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___175_12357.erase_universes);
                                        allow_unbound_universes =
                                          (uu___175_12357.allow_unbound_universes);
                                        reify_ = (uu___175_12357.reify_);
                                        compress_uvars =
                                          (uu___175_12357.compress_uvars);
                                        no_full_norm =
                                          (uu___175_12357.no_full_norm);
                                        check_no_uvars =
                                          (uu___175_12357.check_no_uvars);
                                        unmeta = (uu___175_12357.unmeta);
                                        unascribe =
                                          (uu___175_12357.unascribe);
                                        in_full_norm_request =
                                          (uu___175_12357.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___175_12357.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___174_12354.tcenv);
                                   debug = (uu___174_12354.debug);
                                   delta_level = (uu___174_12354.delta_level);
                                   primitive_steps =
                                     (uu___174_12354.primitive_steps);
                                   strong = (uu___174_12354.strong);
                                   memoize_lazy =
                                     (uu___174_12354.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___174_12354.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12338 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12371 = lookup_bvar env x  in
               (match uu____12371 with
                | Univ uu____12372 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12421 = FStar_ST.op_Bang r  in
                      (match uu____12421 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12543  ->
                                 let uu____12544 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12545 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12544
                                   uu____12545);
                            (let uu____12546 = maybe_weakly_reduced t'  in
                             if uu____12546
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12547 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12618)::uu____12619 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____12629,uu____12630))::stack_rest ->
                    (match c with
                     | Univ uu____12634 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12643 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12664  ->
                                    let uu____12665 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12665);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12705  ->
                                    let uu____12706 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12706);
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
                       (fun uu____12784  ->
                          let uu____12785 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12785);
                     norm cfg env stack1 t1)
                | (Match uu____12786)::uu____12787 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___176_12801 = cfg.steps  in
                             {
                               beta = (uu___176_12801.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_12801.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_12801.unfold_until);
                               unfold_only = (uu___176_12801.unfold_only);
                               unfold_fully = (uu___176_12801.unfold_fully);
                               unfold_attr = (uu___176_12801.unfold_attr);
                               unfold_tac = (uu___176_12801.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_12801.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_12801.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_12801.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_12801.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_12801.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_12801.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_12803 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_12803.tcenv);
                               debug = (uu___177_12803.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_12803.primitive_steps);
                               strong = (uu___177_12803.strong);
                               memoize_lazy = (uu___177_12803.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_12803.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12805 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12805 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12847  -> dummy :: env1) env)
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
                                          let uu____12884 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12884)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_12889 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_12889.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_12889.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12890 -> lopt  in
                           (log cfg
                              (fun uu____12896  ->
                                 let uu____12897 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12897);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_12906 = cfg  in
                               {
                                 steps = (uu___179_12906.steps);
                                 tcenv = (uu___179_12906.tcenv);
                                 debug = (uu___179_12906.debug);
                                 delta_level = (uu___179_12906.delta_level);
                                 primitive_steps =
                                   (uu___179_12906.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_12906.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_12906.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____12917)::uu____12918 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___176_12928 = cfg.steps  in
                             {
                               beta = (uu___176_12928.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_12928.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_12928.unfold_until);
                               unfold_only = (uu___176_12928.unfold_only);
                               unfold_fully = (uu___176_12928.unfold_fully);
                               unfold_attr = (uu___176_12928.unfold_attr);
                               unfold_tac = (uu___176_12928.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_12928.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_12928.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_12928.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_12928.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_12928.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_12928.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_12930 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_12930.tcenv);
                               debug = (uu___177_12930.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_12930.primitive_steps);
                               strong = (uu___177_12930.strong);
                               memoize_lazy = (uu___177_12930.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_12930.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12932 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12932 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12974  -> dummy :: env1) env)
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
                                          let uu____13011 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13011)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_13016 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_13016.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_13016.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13017 -> lopt  in
                           (log cfg
                              (fun uu____13023  ->
                                 let uu____13024 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13024);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_13033 = cfg  in
                               {
                                 steps = (uu___179_13033.steps);
                                 tcenv = (uu___179_13033.tcenv);
                                 debug = (uu___179_13033.debug);
                                 delta_level = (uu___179_13033.delta_level);
                                 primitive_steps =
                                   (uu___179_13033.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_13033.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_13033.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13044)::uu____13045 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___176_13057 = cfg.steps  in
                             {
                               beta = (uu___176_13057.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_13057.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_13057.unfold_until);
                               unfold_only = (uu___176_13057.unfold_only);
                               unfold_fully = (uu___176_13057.unfold_fully);
                               unfold_attr = (uu___176_13057.unfold_attr);
                               unfold_tac = (uu___176_13057.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_13057.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_13057.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_13057.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_13057.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_13057.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_13057.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_13059 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_13059.tcenv);
                               debug = (uu___177_13059.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_13059.primitive_steps);
                               strong = (uu___177_13059.strong);
                               memoize_lazy = (uu___177_13059.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_13059.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13061 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13061 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13103  -> dummy :: env1) env)
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
                                          let uu____13140 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13140)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_13145 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_13145.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_13145.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13146 -> lopt  in
                           (log cfg
                              (fun uu____13152  ->
                                 let uu____13153 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13153);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_13162 = cfg  in
                               {
                                 steps = (uu___179_13162.steps);
                                 tcenv = (uu___179_13162.tcenv);
                                 debug = (uu___179_13162.debug);
                                 delta_level = (uu___179_13162.delta_level);
                                 primitive_steps =
                                   (uu___179_13162.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_13162.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_13162.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13173)::uu____13174 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___176_13188 = cfg.steps  in
                             {
                               beta = (uu___176_13188.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_13188.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_13188.unfold_until);
                               unfold_only = (uu___176_13188.unfold_only);
                               unfold_fully = (uu___176_13188.unfold_fully);
                               unfold_attr = (uu___176_13188.unfold_attr);
                               unfold_tac = (uu___176_13188.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_13188.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_13188.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_13188.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_13188.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_13188.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_13188.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_13190 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_13190.tcenv);
                               debug = (uu___177_13190.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_13190.primitive_steps);
                               strong = (uu___177_13190.strong);
                               memoize_lazy = (uu___177_13190.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_13190.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13192 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13192 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13234  -> dummy :: env1) env)
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
                                          let uu____13271 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13271)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_13276 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_13276.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_13276.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13277 -> lopt  in
                           (log cfg
                              (fun uu____13283  ->
                                 let uu____13284 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13284);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_13293 = cfg  in
                               {
                                 steps = (uu___179_13293.steps);
                                 tcenv = (uu___179_13293.tcenv);
                                 debug = (uu___179_13293.debug);
                                 delta_level = (uu___179_13293.delta_level);
                                 primitive_steps =
                                   (uu___179_13293.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_13293.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_13293.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13304)::uu____13305 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___176_13319 = cfg.steps  in
                             {
                               beta = (uu___176_13319.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_13319.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_13319.unfold_until);
                               unfold_only = (uu___176_13319.unfold_only);
                               unfold_fully = (uu___176_13319.unfold_fully);
                               unfold_attr = (uu___176_13319.unfold_attr);
                               unfold_tac = (uu___176_13319.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_13319.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_13319.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_13319.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_13319.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_13319.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_13319.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_13321 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_13321.tcenv);
                               debug = (uu___177_13321.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_13321.primitive_steps);
                               strong = (uu___177_13321.strong);
                               memoize_lazy = (uu___177_13321.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_13321.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13323 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13323 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13365  -> dummy :: env1) env)
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
                                          let uu____13402 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13402)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_13407 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_13407.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_13407.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13408 -> lopt  in
                           (log cfg
                              (fun uu____13414  ->
                                 let uu____13415 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13415);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_13424 = cfg  in
                               {
                                 steps = (uu___179_13424.steps);
                                 tcenv = (uu___179_13424.tcenv);
                                 debug = (uu___179_13424.debug);
                                 delta_level = (uu___179_13424.delta_level);
                                 primitive_steps =
                                   (uu___179_13424.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_13424.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_13424.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13435)::uu____13436 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___176_13454 = cfg.steps  in
                             {
                               beta = (uu___176_13454.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_13454.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_13454.unfold_until);
                               unfold_only = (uu___176_13454.unfold_only);
                               unfold_fully = (uu___176_13454.unfold_fully);
                               unfold_attr = (uu___176_13454.unfold_attr);
                               unfold_tac = (uu___176_13454.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_13454.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_13454.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_13454.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_13454.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_13454.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_13454.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_13456 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_13456.tcenv);
                               debug = (uu___177_13456.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_13456.primitive_steps);
                               strong = (uu___177_13456.strong);
                               memoize_lazy = (uu___177_13456.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_13456.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13458 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13458 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13500  -> dummy :: env1) env)
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
                                          let uu____13537 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13537)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_13542 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_13542.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_13542.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13543 -> lopt  in
                           (log cfg
                              (fun uu____13549  ->
                                 let uu____13550 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13550);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_13559 = cfg  in
                               {
                                 steps = (uu___179_13559.steps);
                                 tcenv = (uu___179_13559.tcenv);
                                 debug = (uu___179_13559.debug);
                                 delta_level = (uu___179_13559.delta_level);
                                 primitive_steps =
                                   (uu___179_13559.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_13559.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_13559.normalize_pure_lets)
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
                             let uu___176_13573 = cfg.steps  in
                             {
                               beta = (uu___176_13573.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___176_13573.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___176_13573.unfold_until);
                               unfold_only = (uu___176_13573.unfold_only);
                               unfold_fully = (uu___176_13573.unfold_fully);
                               unfold_attr = (uu___176_13573.unfold_attr);
                               unfold_tac = (uu___176_13573.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___176_13573.erase_universes);
                               allow_unbound_universes =
                                 (uu___176_13573.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___176_13573.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___176_13573.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___176_13573.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___176_13573.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___177_13575 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___177_13575.tcenv);
                               debug = (uu___177_13575.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___177_13575.primitive_steps);
                               strong = (uu___177_13575.strong);
                               memoize_lazy = (uu___177_13575.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___177_13575.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13577 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13577 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13619  -> dummy :: env1) env)
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
                                          let uu____13656 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13656)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___178_13661 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___178_13661.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___178_13661.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13662 -> lopt  in
                           (log cfg
                              (fun uu____13668  ->
                                 let uu____13669 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13669);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___179_13678 = cfg  in
                               {
                                 steps = (uu___179_13678.steps);
                                 tcenv = (uu___179_13678.tcenv);
                                 debug = (uu___179_13678.debug);
                                 delta_level = (uu___179_13678.delta_level);
                                 primitive_steps =
                                   (uu___179_13678.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___179_13678.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___179_13678.normalize_pure_lets)
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
                      (fun uu____13727  ->
                         fun stack1  ->
                           match uu____13727 with
                           | (a,aq) ->
                               let uu____13739 =
                                 let uu____13740 =
                                   let uu____13747 =
                                     let uu____13748 =
                                       let uu____13779 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13779, false)  in
                                     Clos uu____13748  in
                                   (uu____13747, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13740  in
                               uu____13739 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13863  ->
                     let uu____13864 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13864);
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
                             ((let uu___180_13900 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___180_13900.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___180_13900.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13901 ->
                      let uu____13906 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13906)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13909 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13909 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13940 =
                          let uu____13941 =
                            let uu____13948 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___181_13950 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___181_13950.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___181_13950.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13948)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13941  in
                        mk uu____13940 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13969 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13969
               else
                 (let uu____13971 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13971 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13979 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14003  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13979 c1  in
                      let t2 =
                        let uu____14025 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14025 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14136)::uu____14137 ->
                    (log cfg
                       (fun uu____14150  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14151)::uu____14152 ->
                    (log cfg
                       (fun uu____14163  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14164,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14165;
                                   FStar_Syntax_Syntax.vars = uu____14166;_},uu____14167,uu____14168))::uu____14169
                    ->
                    (log cfg
                       (fun uu____14178  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14179)::uu____14180 ->
                    (log cfg
                       (fun uu____14191  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14192 ->
                    (log cfg
                       (fun uu____14195  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14199  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14216 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14216
                         | FStar_Util.Inr c ->
                             let uu____14224 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14224
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14237 =
                               let uu____14238 =
                                 let uu____14265 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14265, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14238
                                in
                             mk uu____14237 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14284 ->
                           let uu____14285 =
                             let uu____14286 =
                               let uu____14287 =
                                 let uu____14314 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14314, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14287
                                in
                             mk uu____14286 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14285))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___182_14391 = cfg  in
                   {
                     steps =
                       (let uu___183_14394 = cfg.steps  in
                        {
                          beta = (uu___183_14394.beta);
                          iota = (uu___183_14394.iota);
                          zeta = (uu___183_14394.zeta);
                          weak = true;
                          hnf = (uu___183_14394.hnf);
                          primops = (uu___183_14394.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_14394.do_not_unfold_pure_lets);
                          unfold_until = (uu___183_14394.unfold_until);
                          unfold_only = (uu___183_14394.unfold_only);
                          unfold_fully = (uu___183_14394.unfold_fully);
                          unfold_attr = (uu___183_14394.unfold_attr);
                          unfold_tac = (uu___183_14394.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___183_14394.pure_subterms_within_computations);
                          simplify = (uu___183_14394.simplify);
                          erase_universes = (uu___183_14394.erase_universes);
                          allow_unbound_universes =
                            (uu___183_14394.allow_unbound_universes);
                          reify_ = (uu___183_14394.reify_);
                          compress_uvars = (uu___183_14394.compress_uvars);
                          no_full_norm = (uu___183_14394.no_full_norm);
                          check_no_uvars = (uu___183_14394.check_no_uvars);
                          unmeta = (uu___183_14394.unmeta);
                          unascribe = (uu___183_14394.unascribe);
                          in_full_norm_request =
                            (uu___183_14394.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___183_14394.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___182_14391.tcenv);
                     debug = (uu___182_14391.debug);
                     delta_level = (uu___182_14391.delta_level);
                     primitive_steps = (uu___182_14391.primitive_steps);
                     strong = (uu___182_14391.strong);
                     memoize_lazy = (uu___182_14391.memoize_lazy);
                     normalize_pure_lets =
                       (uu___182_14391.normalize_pure_lets)
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
                         let uu____14430 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14430 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___184_14450 = cfg  in
                               let uu____14451 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___184_14450.steps);
                                 tcenv = uu____14451;
                                 debug = (uu___184_14450.debug);
                                 delta_level = (uu___184_14450.delta_level);
                                 primitive_steps =
                                   (uu___184_14450.primitive_steps);
                                 strong = (uu___184_14450.strong);
                                 memoize_lazy = (uu___184_14450.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_14450.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14458 =
                                 let uu____14459 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14459  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14458
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___185_14462 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___185_14462.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___185_14462.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___185_14462.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___185_14462.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14463 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14463
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14474,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14475;
                               FStar_Syntax_Syntax.lbunivs = uu____14476;
                               FStar_Syntax_Syntax.lbtyp = uu____14477;
                               FStar_Syntax_Syntax.lbeff = uu____14478;
                               FStar_Syntax_Syntax.lbdef = uu____14479;
                               FStar_Syntax_Syntax.lbattrs = uu____14480;
                               FStar_Syntax_Syntax.lbpos = uu____14481;_}::uu____14482),uu____14483)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14523 =
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
               if uu____14523
               then
                 let binder =
                   let uu____14525 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14525  in
                 let env1 =
                   let uu____14535 =
                     let uu____14542 =
                       let uu____14543 =
                         let uu____14574 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14574,
                           false)
                          in
                       Clos uu____14543  in
                     ((FStar_Pervasives_Native.Some binder), uu____14542)  in
                   uu____14535 :: env  in
                 (log cfg
                    (fun uu____14667  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14671  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14672 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14672))
                 else
                   (let uu____14674 =
                      let uu____14679 =
                        let uu____14680 =
                          let uu____14681 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14681
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14680]  in
                      FStar_Syntax_Subst.open_term uu____14679 body  in
                    match uu____14674 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14690  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14698 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14698  in
                            FStar_Util.Inl
                              (let uu___186_14708 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___186_14708.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___186_14708.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14711  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___187_14713 = lb  in
                             let uu____14714 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___187_14713.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___187_14713.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14714;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___187_14713.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___187_14713.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14749  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___188_14772 = cfg  in
                             {
                               steps = (uu___188_14772.steps);
                               tcenv = (uu___188_14772.tcenv);
                               debug = (uu___188_14772.debug);
                               delta_level = (uu___188_14772.delta_level);
                               primitive_steps =
                                 (uu___188_14772.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___188_14772.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___188_14772.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14775  ->
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
               let uu____14792 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14792 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14828 =
                               let uu___189_14829 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___189_14829.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___189_14829.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14828  in
                           let uu____14830 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14830 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14856 =
                                   FStar_List.map (fun uu____14872  -> dummy)
                                     lbs1
                                    in
                                 let uu____14873 =
                                   let uu____14882 =
                                     FStar_List.map
                                       (fun uu____14902  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14882 env  in
                                 FStar_List.append uu____14856 uu____14873
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14926 =
                                       let uu___190_14927 = rc  in
                                       let uu____14928 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___190_14927.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14928;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___190_14927.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14926
                                 | uu____14935 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___191_14939 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___191_14939.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___191_14939.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___191_14939.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___191_14939.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14949 =
                        FStar_List.map (fun uu____14965  -> dummy) lbs2  in
                      FStar_List.append uu____14949 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14973 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14973 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___192_14989 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___192_14989.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___192_14989.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15016 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15016
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15035 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15111  ->
                        match uu____15111 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___193_15232 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___193_15232.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___193_15232.FStar_Syntax_Syntax.sort)
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
               (match uu____15035 with
                | (rec_env,memos,uu____15445) ->
                    let uu____15498 =
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
                             let uu____15821 =
                               let uu____15828 =
                                 let uu____15829 =
                                   let uu____15860 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15860, false)
                                    in
                                 Clos uu____15829  in
                               (FStar_Pervasives_Native.None, uu____15828)
                                in
                             uu____15821 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15970  ->
                     let uu____15971 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15971);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15993 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15995::uu____15996 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16001) ->
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
                             | uu____16024 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16038 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16038
                              | uu____16049 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16053 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16079 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16097 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16114 =
                        let uu____16115 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16116 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16115 uu____16116
                         in
                      failwith uu____16114
                    else rebuild cfg env stack t2
                | uu____16118 -> norm cfg env stack t2))

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
                let uu____16128 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16128  in
              let uu____16129 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16129 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16142  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16153  ->
                        let uu____16154 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16155 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16154 uu____16155);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16160 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16160 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16169))::stack1 ->
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
                      | uu____16224 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16227 ->
                          let uu____16230 =
                            let uu____16231 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16231
                             in
                          failwith uu____16230
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
                  let uu___194_16255 = cfg  in
                  let uu____16256 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16256;
                    tcenv = (uu___194_16255.tcenv);
                    debug = (uu___194_16255.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___194_16255.primitive_steps);
                    strong = (uu___194_16255.strong);
                    memoize_lazy = (uu___194_16255.memoize_lazy);
                    normalize_pure_lets =
                      (uu___194_16255.normalize_pure_lets)
                  }
                else
                  (let uu___195_16258 = cfg  in
                   {
                     steps =
                       (let uu___196_16261 = cfg.steps  in
                        {
                          beta = (uu___196_16261.beta);
                          iota = (uu___196_16261.iota);
                          zeta = false;
                          weak = (uu___196_16261.weak);
                          hnf = (uu___196_16261.hnf);
                          primops = (uu___196_16261.primops);
                          do_not_unfold_pure_lets =
                            (uu___196_16261.do_not_unfold_pure_lets);
                          unfold_until = (uu___196_16261.unfold_until);
                          unfold_only = (uu___196_16261.unfold_only);
                          unfold_fully = (uu___196_16261.unfold_fully);
                          unfold_attr = (uu___196_16261.unfold_attr);
                          unfold_tac = (uu___196_16261.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___196_16261.pure_subterms_within_computations);
                          simplify = (uu___196_16261.simplify);
                          erase_universes = (uu___196_16261.erase_universes);
                          allow_unbound_universes =
                            (uu___196_16261.allow_unbound_universes);
                          reify_ = (uu___196_16261.reify_);
                          compress_uvars = (uu___196_16261.compress_uvars);
                          no_full_norm = (uu___196_16261.no_full_norm);
                          check_no_uvars = (uu___196_16261.check_no_uvars);
                          unmeta = (uu___196_16261.unmeta);
                          unascribe = (uu___196_16261.unascribe);
                          in_full_norm_request =
                            (uu___196_16261.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___196_16261.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___195_16258.tcenv);
                     debug = (uu___195_16258.debug);
                     delta_level = (uu___195_16258.delta_level);
                     primitive_steps = (uu___195_16258.primitive_steps);
                     strong = (uu___195_16258.strong);
                     memoize_lazy = (uu___195_16258.memoize_lazy);
                     normalize_pure_lets =
                       (uu___195_16258.normalize_pure_lets)
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
                  (fun uu____16291  ->
                     let uu____16292 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16293 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16292
                       uu____16293);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16295 =
                   let uu____16296 = FStar_Syntax_Subst.compress head3  in
                   uu____16296.FStar_Syntax_Syntax.n  in
                 match uu____16295 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16314 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16314
                        in
                     let uu____16315 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16315 with
                      | (uu____16316,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16322 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16332 =
                                   let uu____16333 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16333.FStar_Syntax_Syntax.n  in
                                 match uu____16332 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16339,uu____16340))
                                     ->
                                     let uu____16349 =
                                       let uu____16350 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16350.FStar_Syntax_Syntax.n  in
                                     (match uu____16349 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16356,msrc,uu____16358))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16367 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16367
                                      | uu____16368 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16369 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16370 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16370 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___197_16375 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___197_16375.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___197_16375.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___197_16375.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___197_16375.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___197_16375.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16376 = FStar_List.tl stack  in
                                    let uu____16377 =
                                      let uu____16378 =
                                        let uu____16385 =
                                          let uu____16386 =
                                            let uu____16399 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16399)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16386
                                           in
                                        FStar_Syntax_Syntax.mk uu____16385
                                         in
                                      uu____16378
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16376 uu____16377
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16415 =
                                      let uu____16416 = is_return body  in
                                      match uu____16416 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16420;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16421;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16426 -> false  in
                                    if uu____16415
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
                                         let uu____16449 =
                                           let uu____16456 =
                                             let uu____16457 =
                                               let uu____16474 =
                                                 let uu____16477 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16477]  in
                                               (uu____16474, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16457
                                              in
                                           FStar_Syntax_Syntax.mk uu____16456
                                            in
                                         uu____16449
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16495 =
                                           let uu____16496 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16496.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16495 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16502::uu____16503::[])
                                             ->
                                             let uu____16510 =
                                               let uu____16517 =
                                                 let uu____16518 =
                                                   let uu____16525 =
                                                     let uu____16528 =
                                                       let uu____16529 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16529
                                                        in
                                                     let uu____16530 =
                                                       let uu____16533 =
                                                         let uu____16534 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16534
                                                          in
                                                       [uu____16533]  in
                                                     uu____16528 ::
                                                       uu____16530
                                                      in
                                                   (bind1, uu____16525)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16518
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16517
                                                in
                                             uu____16510
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16542 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16548 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16548
                                         then
                                           let uu____16551 =
                                             let uu____16552 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16552
                                              in
                                           let uu____16553 =
                                             let uu____16556 =
                                               let uu____16557 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16557
                                                in
                                             [uu____16556]  in
                                           uu____16551 :: uu____16553
                                         else []  in
                                       let reified =
                                         let uu____16562 =
                                           let uu____16569 =
                                             let uu____16570 =
                                               let uu____16585 =
                                                 let uu____16588 =
                                                   let uu____16591 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16592 =
                                                     let uu____16595 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16595]  in
                                                   uu____16591 :: uu____16592
                                                    in
                                                 let uu____16596 =
                                                   let uu____16599 =
                                                     let uu____16602 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16603 =
                                                       let uu____16606 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16607 =
                                                         let uu____16610 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16611 =
                                                           let uu____16614 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16614]  in
                                                         uu____16610 ::
                                                           uu____16611
                                                          in
                                                       uu____16606 ::
                                                         uu____16607
                                                        in
                                                     uu____16602 ::
                                                       uu____16603
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16599
                                                    in
                                                 FStar_List.append
                                                   uu____16588 uu____16596
                                                  in
                                               (bind_inst, uu____16585)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16570
                                              in
                                           FStar_Syntax_Syntax.mk uu____16569
                                            in
                                         uu____16562
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16626  ->
                                            let uu____16627 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16628 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16627 uu____16628);
                                       (let uu____16629 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16629 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16653 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16653
                        in
                     let uu____16654 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16654 with
                      | (uu____16655,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16694 =
                                  let uu____16695 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16695.FStar_Syntax_Syntax.n  in
                                match uu____16694 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16701) -> t2
                                | uu____16706 -> head4  in
                              let uu____16707 =
                                let uu____16708 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16708.FStar_Syntax_Syntax.n  in
                              match uu____16707 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16714 -> FStar_Pervasives_Native.None
                               in
                            let uu____16715 = maybe_extract_fv head4  in
                            match uu____16715 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16725 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16725
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16730 = maybe_extract_fv head5
                                     in
                                  match uu____16730 with
                                  | FStar_Pervasives_Native.Some uu____16735
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16736 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16741 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16758 =
                              match uu____16758 with
                              | (e,q) ->
                                  let uu____16765 =
                                    let uu____16766 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16766.FStar_Syntax_Syntax.n  in
                                  (match uu____16765 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16781 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16781
                                   | uu____16782 -> false)
                               in
                            let uu____16783 =
                              let uu____16784 =
                                let uu____16791 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16791 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16784
                               in
                            if uu____16783
                            then
                              let uu____16796 =
                                let uu____16797 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16797
                                 in
                              failwith uu____16796
                            else ());
                           (let uu____16799 = maybe_unfold_action head_app
                               in
                            match uu____16799 with
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
                                   (fun uu____16842  ->
                                      let uu____16843 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16844 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16843 uu____16844);
                                 (let uu____16845 = FStar_List.tl stack  in
                                  norm cfg env uu____16845 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16847) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16871 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16871  in
                     (log cfg
                        (fun uu____16875  ->
                           let uu____16876 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16876);
                      (let uu____16877 = FStar_List.tl stack  in
                       norm cfg env uu____16877 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16998  ->
                               match uu____16998 with
                               | (pat,wopt,tm) ->
                                   let uu____17046 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17046)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17078 = FStar_List.tl stack  in
                     norm cfg env uu____17078 tm
                 | uu____17079 -> fallback ())

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
              (fun uu____17093  ->
                 let uu____17094 = FStar_Ident.string_of_lid msrc  in
                 let uu____17095 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17096 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17094
                   uu____17095 uu____17096);
            (let uu____17097 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17097
             then
               let ed =
                 let uu____17099 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17099  in
               let uu____17100 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17100 with
               | (uu____17101,return_repr) ->
                   let return_inst =
                     let uu____17110 =
                       let uu____17111 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17111.FStar_Syntax_Syntax.n  in
                     match uu____17110 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17117::[]) ->
                         let uu____17124 =
                           let uu____17131 =
                             let uu____17132 =
                               let uu____17139 =
                                 let uu____17142 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17142]  in
                               (return_tm, uu____17139)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17132  in
                           FStar_Syntax_Syntax.mk uu____17131  in
                         uu____17124 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17150 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17153 =
                     let uu____17160 =
                       let uu____17161 =
                         let uu____17176 =
                           let uu____17179 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17180 =
                             let uu____17183 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17183]  in
                           uu____17179 :: uu____17180  in
                         (return_inst, uu____17176)  in
                       FStar_Syntax_Syntax.Tm_app uu____17161  in
                     FStar_Syntax_Syntax.mk uu____17160  in
                   uu____17153 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17192 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17192 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17195 =
                      let uu____17196 = FStar_Ident.text_of_lid msrc  in
                      let uu____17197 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17196 uu____17197
                       in
                    failwith uu____17195
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17198;
                      FStar_TypeChecker_Env.mtarget = uu____17199;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17200;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17222 =
                      let uu____17223 = FStar_Ident.text_of_lid msrc  in
                      let uu____17224 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17223 uu____17224
                       in
                    failwith uu____17222
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17225;
                      FStar_TypeChecker_Env.mtarget = uu____17226;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17227;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17262 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17263 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17262 t FStar_Syntax_Syntax.tun uu____17263))

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
                (fun uu____17319  ->
                   match uu____17319 with
                   | (a,imp) ->
                       let uu____17330 = norm cfg env [] a  in
                       (uu____17330, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17338  ->
             let uu____17339 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17340 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17339 uu____17340);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17364 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17364
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___198_17367 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___198_17367.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___198_17367.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17387 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17387
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___199_17390 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___199_17390.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___199_17390.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17425  ->
                      match uu____17425 with
                      | (a,i) ->
                          let uu____17436 = norm cfg env [] a  in
                          (uu____17436, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___114_17454  ->
                       match uu___114_17454 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17458 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17458
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___200_17466 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___201_17469 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___201_17469.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___200_17466.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___200_17466.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17472  ->
        match uu____17472 with
        | (x,imp) ->
            let uu____17475 =
              let uu___202_17476 = x  in
              let uu____17477 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___202_17476.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___202_17476.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17477
              }  in
            (uu____17475, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17483 =
          FStar_List.fold_left
            (fun uu____17501  ->
               fun b  ->
                 match uu____17501 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17483 with | (nbs,uu____17541) -> FStar_List.rev nbs

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
            let uu____17557 =
              let uu___203_17558 = rc  in
              let uu____17559 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___203_17558.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17559;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___203_17558.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17557
        | uu____17566 -> lopt

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
            (let uu____17587 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17588 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17587
               uu____17588)
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
          let uu____17608 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17608
          then tm1
          else
            (let w t =
               let uu___204_17622 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___204_17622.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___204_17622.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17633 =
                 let uu____17634 = FStar_Syntax_Util.unmeta t  in
                 uu____17634.FStar_Syntax_Syntax.n  in
               match uu____17633 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17641 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17690)::args1,(bv,uu____17693)::bs1) ->
                   let uu____17727 =
                     let uu____17728 = FStar_Syntax_Subst.compress t  in
                     uu____17728.FStar_Syntax_Syntax.n  in
                   (match uu____17727 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17732 -> false)
               | ([],[]) -> true
               | (uu____17753,uu____17754) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17795 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17796 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17795
                    uu____17796)
               else ();
               (let uu____17798 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17798 with
                | (hd1,args) ->
                    let uu____17831 =
                      let uu____17832 = FStar_Syntax_Subst.compress hd1  in
                      uu____17832.FStar_Syntax_Syntax.n  in
                    (match uu____17831 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____17839 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17840 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17841 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17839 uu____17840 uu____17841)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17843 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17860 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17861 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17860
                    uu____17861)
               else ();
               (let uu____17863 = FStar_Syntax_Util.is_squash t  in
                match uu____17863 with
                | FStar_Pervasives_Native.Some (uu____17874,t') ->
                    is_applied bs t'
                | uu____17886 ->
                    let uu____17895 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17895 with
                     | FStar_Pervasives_Native.Some (uu____17906,t') ->
                         is_applied bs t'
                     | uu____17918 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17942 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17942 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17949)::(q,uu____17951)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____17987 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17988 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17987 uu____17988)
                    else ();
                    (let uu____17990 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17990 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17995 =
                           let uu____17996 = FStar_Syntax_Subst.compress p
                              in
                           uu____17996.FStar_Syntax_Syntax.n  in
                         (match uu____17995 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18004 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18004))
                          | uu____18005 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18008)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18033 =
                           let uu____18034 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18034.FStar_Syntax_Syntax.n  in
                         (match uu____18033 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18042 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18042))
                          | uu____18043 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18047 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18047 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18052 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18052 with
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
                                     let uu____18061 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18061))
                               | uu____18062 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18067)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18092 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18092 with
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
                                     let uu____18101 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18101))
                               | uu____18102 -> FStar_Pervasives_Native.None)
                          | uu____18105 -> FStar_Pervasives_Native.None)
                     | uu____18108 -> FStar_Pervasives_Native.None))
               | uu____18111 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18124 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18124 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18130)::[],uu____18131,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18148 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18149 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18148
                         uu____18149)
                    else ();
                    is_quantified_const bv phi')
               | uu____18151 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18164 =
                 let uu____18165 = FStar_Syntax_Subst.compress phi  in
                 uu____18165.FStar_Syntax_Syntax.n  in
               match uu____18164 with
               | FStar_Syntax_Syntax.Tm_match (uu____18170,br::brs) ->
                   let uu____18237 = br  in
                   (match uu____18237 with
                    | (uu____18254,uu____18255,e) ->
                        let r =
                          let uu____18276 = simp_t e  in
                          match uu____18276 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18282 =
                                FStar_List.for_all
                                  (fun uu____18300  ->
                                     match uu____18300 with
                                     | (uu____18313,uu____18314,e') ->
                                         let uu____18328 = simp_t e'  in
                                         uu____18328 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18282
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18336 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18343 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18343
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18368 =
                 match uu____18368 with
                 | (t1,q) ->
                     let uu____18381 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18381 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18409 -> (t1, q))
                  in
               let uu____18418 = FStar_Syntax_Util.head_and_args t  in
               match uu____18418 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18482 =
                 let uu____18483 = FStar_Syntax_Util.unmeta ty  in
                 uu____18483.FStar_Syntax_Syntax.n  in
               match uu____18482 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18487) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18492,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18512 -> false  in
             let simplify1 arg =
               let uu____18537 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18537, arg)  in
             let uu____18546 = is_forall_const tm1  in
             match uu____18546 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____18551 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18552 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18551
                       uu____18552)
                  else ();
                  (let uu____18554 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18554))
             | FStar_Pervasives_Native.None  ->
                 let uu____18555 =
                   let uu____18556 = FStar_Syntax_Subst.compress tm1  in
                   uu____18556.FStar_Syntax_Syntax.n  in
                 (match uu____18555 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18560;
                              FStar_Syntax_Syntax.vars = uu____18561;_},uu____18562);
                         FStar_Syntax_Syntax.pos = uu____18563;
                         FStar_Syntax_Syntax.vars = uu____18564;_},args)
                      ->
                      let uu____18590 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18590
                      then
                        let uu____18591 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18591 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18638)::
                             (uu____18639,(arg,uu____18641))::[] ->
                             maybe_auto_squash arg
                         | (uu____18690,(arg,uu____18692))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18693)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18742)::uu____18743::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18794::(FStar_Pervasives_Native.Some (false
                                         ),uu____18795)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18846 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18860 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18860
                         then
                           let uu____18861 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18861 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18908)::uu____18909::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18960::(FStar_Pervasives_Native.Some (true
                                           ),uu____18961)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19012)::(uu____19013,(arg,uu____19015))::[]
                               -> maybe_auto_squash arg
                           | (uu____19064,(arg,uu____19066))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19067)::[]
                               -> maybe_auto_squash arg
                           | uu____19116 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19130 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19130
                            then
                              let uu____19131 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19131 with
                              | uu____19178::(FStar_Pervasives_Native.Some
                                              (true ),uu____19179)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19230)::uu____19231::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19282)::(uu____19283,(arg,uu____19285))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19334,(p,uu____19336))::(uu____19337,
                                                                (q,uu____19339))::[]
                                  ->
                                  let uu____19386 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19386
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19388 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19402 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19402
                               then
                                 let uu____19403 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19403 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19450)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19451)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19502)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19503)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19554)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19555)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19606)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19607)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19658,(arg,uu____19660))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19661)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19710)::(uu____19711,(arg,uu____19713))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19762,(arg,uu____19764))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19765)::[]
                                     ->
                                     let uu____19814 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19814
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19815)::(uu____19816,(arg,uu____19818))::[]
                                     ->
                                     let uu____19867 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19867
                                 | (uu____19868,(p,uu____19870))::(uu____19871,
                                                                   (q,uu____19873))::[]
                                     ->
                                     let uu____19920 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19920
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19922 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19936 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19936
                                  then
                                    let uu____19937 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19937 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19984)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20015)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20046 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20060 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20060
                                     then
                                       match args with
                                       | (t,uu____20062)::[] ->
                                           let uu____20079 =
                                             let uu____20080 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20080.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20079 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20083::[],body,uu____20085)
                                                ->
                                                let uu____20112 = simp_t body
                                                   in
                                                (match uu____20112 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20115 -> tm1)
                                            | uu____20118 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20120))::(t,uu____20122)::[]
                                           ->
                                           let uu____20161 =
                                             let uu____20162 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20162.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20161 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20165::[],body,uu____20167)
                                                ->
                                                let uu____20194 = simp_t body
                                                   in
                                                (match uu____20194 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20197 -> tm1)
                                            | uu____20200 -> tm1)
                                       | uu____20201 -> tm1
                                     else
                                       (let uu____20211 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20211
                                        then
                                          match args with
                                          | (t,uu____20213)::[] ->
                                              let uu____20230 =
                                                let uu____20231 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20231.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20230 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20234::[],body,uu____20236)
                                                   ->
                                                   let uu____20263 =
                                                     simp_t body  in
                                                   (match uu____20263 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20266 -> tm1)
                                               | uu____20269 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20271))::(t,uu____20273)::[]
                                              ->
                                              let uu____20312 =
                                                let uu____20313 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20313.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20312 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20316::[],body,uu____20318)
                                                   ->
                                                   let uu____20345 =
                                                     simp_t body  in
                                                   (match uu____20345 with
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
                                                    | uu____20348 -> tm1)
                                               | uu____20351 -> tm1)
                                          | uu____20352 -> tm1
                                        else
                                          (let uu____20362 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20362
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20363;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20364;_},uu____20365)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20382;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20383;_},uu____20384)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20401 -> tm1
                                           else
                                             (let uu____20411 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20411 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20431 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20441;
                         FStar_Syntax_Syntax.vars = uu____20442;_},args)
                      ->
                      let uu____20464 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20464
                      then
                        let uu____20465 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20465 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20512)::
                             (uu____20513,(arg,uu____20515))::[] ->
                             maybe_auto_squash arg
                         | (uu____20564,(arg,uu____20566))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20567)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20616)::uu____20617::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20668::(FStar_Pervasives_Native.Some (false
                                         ),uu____20669)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20720 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20734 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20734
                         then
                           let uu____20735 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20735 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20782)::uu____20783::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20834::(FStar_Pervasives_Native.Some (true
                                           ),uu____20835)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20886)::(uu____20887,(arg,uu____20889))::[]
                               -> maybe_auto_squash arg
                           | (uu____20938,(arg,uu____20940))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20941)::[]
                               -> maybe_auto_squash arg
                           | uu____20990 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21004 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21004
                            then
                              let uu____21005 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21005 with
                              | uu____21052::(FStar_Pervasives_Native.Some
                                              (true ),uu____21053)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21104)::uu____21105::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21156)::(uu____21157,(arg,uu____21159))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21208,(p,uu____21210))::(uu____21211,
                                                                (q,uu____21213))::[]
                                  ->
                                  let uu____21260 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21260
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21262 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21276 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21276
                               then
                                 let uu____21277 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21277 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21324)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21325)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21376)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21377)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21428)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21429)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21480)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21481)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21532,(arg,uu____21534))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21535)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21584)::(uu____21585,(arg,uu____21587))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21636,(arg,uu____21638))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21639)::[]
                                     ->
                                     let uu____21688 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21688
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21689)::(uu____21690,(arg,uu____21692))::[]
                                     ->
                                     let uu____21741 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21741
                                 | (uu____21742,(p,uu____21744))::(uu____21745,
                                                                   (q,uu____21747))::[]
                                     ->
                                     let uu____21794 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21794
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21796 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21810 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21810
                                  then
                                    let uu____21811 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21811 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21858)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21889)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21920 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21934 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21934
                                     then
                                       match args with
                                       | (t,uu____21936)::[] ->
                                           let uu____21953 =
                                             let uu____21954 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21954.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21953 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21957::[],body,uu____21959)
                                                ->
                                                let uu____21986 = simp_t body
                                                   in
                                                (match uu____21986 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21989 -> tm1)
                                            | uu____21992 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21994))::(t,uu____21996)::[]
                                           ->
                                           let uu____22035 =
                                             let uu____22036 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22036.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22035 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22039::[],body,uu____22041)
                                                ->
                                                let uu____22068 = simp_t body
                                                   in
                                                (match uu____22068 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22071 -> tm1)
                                            | uu____22074 -> tm1)
                                       | uu____22075 -> tm1
                                     else
                                       (let uu____22085 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22085
                                        then
                                          match args with
                                          | (t,uu____22087)::[] ->
                                              let uu____22104 =
                                                let uu____22105 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22105.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22104 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22108::[],body,uu____22110)
                                                   ->
                                                   let uu____22137 =
                                                     simp_t body  in
                                                   (match uu____22137 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22140 -> tm1)
                                               | uu____22143 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22145))::(t,uu____22147)::[]
                                              ->
                                              let uu____22186 =
                                                let uu____22187 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22187.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22186 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22190::[],body,uu____22192)
                                                   ->
                                                   let uu____22219 =
                                                     simp_t body  in
                                                   (match uu____22219 with
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
                                                    | uu____22222 -> tm1)
                                               | uu____22225 -> tm1)
                                          | uu____22226 -> tm1
                                        else
                                          (let uu____22236 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22236
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22237;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22238;_},uu____22239)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22256;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22257;_},uu____22258)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22275 -> tm1
                                           else
                                             (let uu____22285 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22285 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22305 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22320 = simp_t t  in
                      (match uu____22320 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22323 ->
                      let uu____22346 = is_const_match tm1  in
                      (match uu____22346 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22349 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22359  ->
               (let uu____22361 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22362 = FStar_Syntax_Print.term_to_string t  in
                let uu____22363 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22370 =
                  let uu____22371 =
                    let uu____22374 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22374
                     in
                  stack_to_string uu____22371  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22361 uu____22362 uu____22363 uu____22370);
               (let uu____22397 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22397
                then
                  let uu____22398 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22398 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22405 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22406 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22407 =
                          let uu____22408 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22408
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22405
                          uu____22406 uu____22407);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22426 =
                     let uu____22427 =
                       let uu____22428 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22428  in
                     FStar_Util.string_of_int uu____22427  in
                   let uu____22433 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22434 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22426 uu____22433 uu____22434)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22440,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22489  ->
                     let uu____22490 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22490);
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
               let uu____22526 =
                 let uu___205_22527 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___205_22527.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___205_22527.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22526
           | (Arg (Univ uu____22528,uu____22529,uu____22530))::uu____22531 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22534,uu____22535))::uu____22536 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22551,uu____22552),aq,r))::stack1
               when
               let uu____22602 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22602 ->
               let t2 =
                 let uu____22606 =
                   let uu____22611 =
                     let uu____22612 = closure_as_term cfg env_arg tm  in
                     (uu____22612, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22611  in
                 uu____22606 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22618),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22671  ->
                     let uu____22672 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22672);
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
                  (let uu____22682 = FStar_ST.op_Bang m  in
                   match uu____22682 with
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
                   | FStar_Pervasives_Native.Some (uu____22823,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22874 =
                 log cfg
                   (fun uu____22878  ->
                      let uu____22879 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22879);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22883 =
                 let uu____22884 = FStar_Syntax_Subst.compress t1  in
                 uu____22884.FStar_Syntax_Syntax.n  in
               (match uu____22883 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22911 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22911  in
                    (log cfg
                       (fun uu____22915  ->
                          let uu____22916 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22916);
                     (let uu____22917 = FStar_List.tl stack  in
                      norm cfg env1 uu____22917 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22918);
                       FStar_Syntax_Syntax.pos = uu____22919;
                       FStar_Syntax_Syntax.vars = uu____22920;_},(e,uu____22922)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22951 when
                    (cfg.steps).primops ->
                    let uu____22966 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22966 with
                     | (hd1,args) ->
                         let uu____23003 =
                           let uu____23004 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23004.FStar_Syntax_Syntax.n  in
                         (match uu____23003 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23008 = find_prim_step cfg fv  in
                              (match uu____23008 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23011; arity = uu____23012;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23014;
                                     requires_binder_substitution =
                                       uu____23015;
                                     interpretation = uu____23016;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23031 -> fallback " (3)" ())
                          | uu____23034 -> fallback " (4)" ()))
                | uu____23035 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23056  ->
                     let uu____23057 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23057);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23066 =
                   log cfg1
                     (fun uu____23071  ->
                        let uu____23072 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23073 =
                          let uu____23074 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23091  ->
                                    match uu____23091 with
                                    | (p,uu____23101,uu____23102) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23074
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23072 uu____23073);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___115_23119  ->
                                match uu___115_23119 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23120 -> false))
                         in
                      let steps =
                        let uu___206_23122 = cfg1.steps  in
                        {
                          beta = (uu___206_23122.beta);
                          iota = (uu___206_23122.iota);
                          zeta = false;
                          weak = (uu___206_23122.weak);
                          hnf = (uu___206_23122.hnf);
                          primops = (uu___206_23122.primops);
                          do_not_unfold_pure_lets =
                            (uu___206_23122.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___206_23122.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___206_23122.pure_subterms_within_computations);
                          simplify = (uu___206_23122.simplify);
                          erase_universes = (uu___206_23122.erase_universes);
                          allow_unbound_universes =
                            (uu___206_23122.allow_unbound_universes);
                          reify_ = (uu___206_23122.reify_);
                          compress_uvars = (uu___206_23122.compress_uvars);
                          no_full_norm = (uu___206_23122.no_full_norm);
                          check_no_uvars = (uu___206_23122.check_no_uvars);
                          unmeta = (uu___206_23122.unmeta);
                          unascribe = (uu___206_23122.unascribe);
                          in_full_norm_request =
                            (uu___206_23122.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___206_23122.weakly_reduce_scrutinee)
                        }  in
                      let uu___207_23127 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___207_23127.tcenv);
                        debug = (uu___207_23127.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___207_23127.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___207_23127.memoize_lazy);
                        normalize_pure_lets =
                          (uu___207_23127.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23167 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23188 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23248  ->
                                    fun uu____23249  ->
                                      match (uu____23248, uu____23249) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23340 = norm_pat env3 p1
                                             in
                                          (match uu____23340 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23188 with
                           | (pats1,env3) ->
                               ((let uu___208_23422 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___208_23422.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___209_23441 = x  in
                            let uu____23442 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___209_23441.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___209_23441.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23442
                            }  in
                          ((let uu___210_23456 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___210_23456.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___211_23467 = x  in
                            let uu____23468 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___211_23467.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___211_23467.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23468
                            }  in
                          ((let uu___212_23482 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___212_23482.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___213_23498 = x  in
                            let uu____23499 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___213_23498.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___213_23498.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23499
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___214_23506 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___214_23506.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23516 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23530 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23530 with
                                  | (p,wopt,e) ->
                                      let uu____23550 = norm_pat env1 p  in
                                      (match uu____23550 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23575 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23575
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23582 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23582
                      then
                        norm
                          (let uu___215_23585 = cfg1  in
                           {
                             steps =
                               (let uu___216_23588 = cfg1.steps  in
                                {
                                  beta = (uu___216_23588.beta);
                                  iota = (uu___216_23588.iota);
                                  zeta = (uu___216_23588.zeta);
                                  weak = (uu___216_23588.weak);
                                  hnf = (uu___216_23588.hnf);
                                  primops = (uu___216_23588.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___216_23588.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___216_23588.unfold_until);
                                  unfold_only = (uu___216_23588.unfold_only);
                                  unfold_fully =
                                    (uu___216_23588.unfold_fully);
                                  unfold_attr = (uu___216_23588.unfold_attr);
                                  unfold_tac = (uu___216_23588.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___216_23588.pure_subterms_within_computations);
                                  simplify = (uu___216_23588.simplify);
                                  erase_universes =
                                    (uu___216_23588.erase_universes);
                                  allow_unbound_universes =
                                    (uu___216_23588.allow_unbound_universes);
                                  reify_ = (uu___216_23588.reify_);
                                  compress_uvars =
                                    (uu___216_23588.compress_uvars);
                                  no_full_norm =
                                    (uu___216_23588.no_full_norm);
                                  check_no_uvars =
                                    (uu___216_23588.check_no_uvars);
                                  unmeta = (uu___216_23588.unmeta);
                                  unascribe = (uu___216_23588.unascribe);
                                  in_full_norm_request =
                                    (uu___216_23588.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___215_23585.tcenv);
                             debug = (uu___215_23585.debug);
                             delta_level = (uu___215_23585.delta_level);
                             primitive_steps =
                               (uu___215_23585.primitive_steps);
                             strong = (uu___215_23585.strong);
                             memoize_lazy = (uu___215_23585.memoize_lazy);
                             normalize_pure_lets =
                               (uu___215_23585.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23590 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23590)
                    in
                 let rec is_cons head1 =
                   let uu____23597 =
                     let uu____23598 = FStar_Syntax_Subst.compress head1  in
                     uu____23598.FStar_Syntax_Syntax.n  in
                   match uu____23597 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23602) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23607 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23608;
                         FStar_Syntax_Syntax.fv_delta = uu____23609;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23610;
                         FStar_Syntax_Syntax.fv_delta = uu____23611;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23612);_}
                       -> true
                   | uu____23619 -> false  in
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
                   let uu____23780 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23780 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23867 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23906 ->
                                 let uu____23907 =
                                   let uu____23908 = is_cons head1  in
                                   Prims.op_Negation uu____23908  in
                                 FStar_Util.Inr uu____23907)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23933 =
                              let uu____23934 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23934.FStar_Syntax_Syntax.n  in
                            (match uu____23933 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23952 ->
                                 let uu____23953 =
                                   let uu____23954 = is_cons head1  in
                                   Prims.op_Negation uu____23954  in
                                 FStar_Util.Inr uu____23953))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24023)::rest_a,(p1,uu____24026)::rest_p) ->
                       let uu____24070 = matches_pat t2 p1  in
                       (match uu____24070 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24119 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24229 = matches_pat scrutinee1 p1  in
                       (match uu____24229 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24269  ->
                                  let uu____24270 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24271 =
                                    let uu____24272 =
                                      FStar_List.map
                                        (fun uu____24282  ->
                                           match uu____24282 with
                                           | (uu____24287,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24272
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24270 uu____24271);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24319  ->
                                       match uu____24319 with
                                       | (bv,t2) ->
                                           let uu____24342 =
                                             let uu____24349 =
                                               let uu____24352 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24352
                                                in
                                             let uu____24353 =
                                               let uu____24354 =
                                                 let uu____24385 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24385, false)
                                                  in
                                               Clos uu____24354  in
                                             (uu____24349, uu____24353)  in
                                           uu____24342 :: env2) env1 s
                                 in
                              let uu____24502 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24502)))
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
    let uu____24529 =
      let uu____24532 = FStar_ST.op_Bang plugins  in p :: uu____24532  in
    FStar_ST.op_Colon_Equals plugins uu____24529  in
  let retrieve uu____24640 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24717  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___116_24758  ->
                  match uu___116_24758 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24762 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24768 -> d  in
        let uu____24771 = to_fsteps s  in
        let uu____24772 =
          let uu____24773 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24774 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24775 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24776 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____24777 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24778 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24773;
            primop = uu____24774;
            b380 = uu____24775;
            wpe = uu____24776;
            norm_delayed = uu____24777;
            print_normalized = uu____24778
          }  in
        let uu____24779 =
          let uu____24782 =
            let uu____24785 = retrieve_plugins ()  in
            FStar_List.append uu____24785 psteps  in
          add_steps built_in_primitive_steps uu____24782  in
        let uu____24788 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24790 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24790)
           in
        {
          steps = uu____24771;
          tcenv = e;
          debug = uu____24772;
          delta_level = d1;
          primitive_steps = uu____24779;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24788
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
      fun t  -> let uu____24872 = config s e  in norm_comp uu____24872 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24889 = config [] env  in norm_universe uu____24889 [] u
  
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
        let uu____24913 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24913  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24920 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___217_24939 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___217_24939.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___217_24939.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24946 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24946
          then
            let ct1 =
              let uu____24948 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24948 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24955 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24955
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___218_24959 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___218_24959.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___218_24959.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___218_24959.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___219_24961 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___219_24961.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___219_24961.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___219_24961.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___219_24961.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___220_24962 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___220_24962.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___220_24962.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24964 -> c
  
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
        let uu____24982 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24982  in
      let uu____24989 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24989
      then
        let uu____24990 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24990 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24996  ->
                 let uu____24997 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24997)
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
            ((let uu____25018 =
                let uu____25023 =
                  let uu____25024 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25024
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25023)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25018);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25039 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25039 [] c
        with
        | e ->
            ((let uu____25052 =
                let uu____25057 =
                  let uu____25058 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25058
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25057)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25052);
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
                   let uu____25103 =
                     let uu____25104 =
                       let uu____25111 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25111)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25104  in
                   mk uu____25103 t01.FStar_Syntax_Syntax.pos
               | uu____25116 -> t2)
          | uu____25117 -> t2  in
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
        let uu____25181 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25181 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25210 ->
                 let uu____25217 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25217 with
                  | (actuals,uu____25227,uu____25228) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25242 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25242 with
                         | (binders,args) ->
                             let uu____25259 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25259
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
      | uu____25271 ->
          let uu____25272 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25272 with
           | (head1,args) ->
               let uu____25309 =
                 let uu____25310 = FStar_Syntax_Subst.compress head1  in
                 uu____25310.FStar_Syntax_Syntax.n  in
               (match uu____25309 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25313,thead) ->
                    let uu____25339 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25339 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25381 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___225_25389 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___225_25389.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___225_25389.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___225_25389.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___225_25389.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___225_25389.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___225_25389.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___225_25389.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___225_25389.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___225_25389.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___225_25389.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___225_25389.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___225_25389.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___225_25389.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___225_25389.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___225_25389.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___225_25389.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___225_25389.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___225_25389.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___225_25389.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___225_25389.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___225_25389.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___225_25389.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___225_25389.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___225_25389.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___225_25389.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___225_25389.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___225_25389.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___225_25389.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___225_25389.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___225_25389.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___225_25389.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___225_25389.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___225_25389.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___225_25389.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25381 with
                            | (uu____25390,ty,uu____25392) ->
                                eta_expand_with_type env t ty))
                | uu____25393 ->
                    let uu____25394 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___226_25402 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___226_25402.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___226_25402.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___226_25402.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___226_25402.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___226_25402.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___226_25402.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___226_25402.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___226_25402.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___226_25402.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___226_25402.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___226_25402.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___226_25402.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___226_25402.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___226_25402.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___226_25402.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___226_25402.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___226_25402.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___226_25402.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___226_25402.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___226_25402.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___226_25402.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___226_25402.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___226_25402.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___226_25402.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___226_25402.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___226_25402.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___226_25402.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___226_25402.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___226_25402.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___226_25402.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___226_25402.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___226_25402.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___226_25402.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___226_25402.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25394 with
                     | (uu____25403,ty,uu____25405) ->
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
      let uu___227_25478 = x  in
      let uu____25479 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___227_25478.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___227_25478.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25479
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25482 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25507 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25508 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25509 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25510 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25517 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25518 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25519 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___228_25549 = rc  in
          let uu____25550 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25557 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___228_25549.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25550;
            FStar_Syntax_Syntax.residual_flags = uu____25557
          }  in
        let uu____25560 =
          let uu____25561 =
            let uu____25578 = elim_delayed_subst_binders bs  in
            let uu____25585 = elim_delayed_subst_term t2  in
            let uu____25586 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25578, uu____25585, uu____25586)  in
          FStar_Syntax_Syntax.Tm_abs uu____25561  in
        mk1 uu____25560
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25615 =
          let uu____25616 =
            let uu____25629 = elim_delayed_subst_binders bs  in
            let uu____25636 = elim_delayed_subst_comp c  in
            (uu____25629, uu____25636)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25616  in
        mk1 uu____25615
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25649 =
          let uu____25650 =
            let uu____25657 = elim_bv bv  in
            let uu____25658 = elim_delayed_subst_term phi  in
            (uu____25657, uu____25658)  in
          FStar_Syntax_Syntax.Tm_refine uu____25650  in
        mk1 uu____25649
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25681 =
          let uu____25682 =
            let uu____25697 = elim_delayed_subst_term t2  in
            let uu____25698 = elim_delayed_subst_args args  in
            (uu____25697, uu____25698)  in
          FStar_Syntax_Syntax.Tm_app uu____25682  in
        mk1 uu____25681
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___229_25764 = p  in
              let uu____25765 =
                let uu____25766 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25766  in
              {
                FStar_Syntax_Syntax.v = uu____25765;
                FStar_Syntax_Syntax.p =
                  (uu___229_25764.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___230_25768 = p  in
              let uu____25769 =
                let uu____25770 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25770  in
              {
                FStar_Syntax_Syntax.v = uu____25769;
                FStar_Syntax_Syntax.p =
                  (uu___230_25768.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___231_25777 = p  in
              let uu____25778 =
                let uu____25779 =
                  let uu____25786 = elim_bv x  in
                  let uu____25787 = elim_delayed_subst_term t0  in
                  (uu____25786, uu____25787)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25779  in
              {
                FStar_Syntax_Syntax.v = uu____25778;
                FStar_Syntax_Syntax.p =
                  (uu___231_25777.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___232_25806 = p  in
              let uu____25807 =
                let uu____25808 =
                  let uu____25821 =
                    FStar_List.map
                      (fun uu____25844  ->
                         match uu____25844 with
                         | (x,b) ->
                             let uu____25857 = elim_pat x  in
                             (uu____25857, b)) pats
                     in
                  (fv, uu____25821)  in
                FStar_Syntax_Syntax.Pat_cons uu____25808  in
              {
                FStar_Syntax_Syntax.v = uu____25807;
                FStar_Syntax_Syntax.p =
                  (uu___232_25806.FStar_Syntax_Syntax.p)
              }
          | uu____25870 -> p  in
        let elim_branch uu____25894 =
          match uu____25894 with
          | (pat,wopt,t3) ->
              let uu____25920 = elim_pat pat  in
              let uu____25923 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25926 = elim_delayed_subst_term t3  in
              (uu____25920, uu____25923, uu____25926)
           in
        let uu____25931 =
          let uu____25932 =
            let uu____25955 = elim_delayed_subst_term t2  in
            let uu____25956 = FStar_List.map elim_branch branches  in
            (uu____25955, uu____25956)  in
          FStar_Syntax_Syntax.Tm_match uu____25932  in
        mk1 uu____25931
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26067 =
          match uu____26067 with
          | (tc,topt) ->
              let uu____26102 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26112 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26112
                | FStar_Util.Inr c ->
                    let uu____26114 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26114
                 in
              let uu____26115 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26102, uu____26115)
           in
        let uu____26124 =
          let uu____26125 =
            let uu____26152 = elim_delayed_subst_term t2  in
            let uu____26153 = elim_ascription a  in
            (uu____26152, uu____26153, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26125  in
        mk1 uu____26124
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___233_26200 = lb  in
          let uu____26201 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26204 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___233_26200.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___233_26200.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26201;
            FStar_Syntax_Syntax.lbeff =
              (uu___233_26200.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26204;
            FStar_Syntax_Syntax.lbattrs =
              (uu___233_26200.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___233_26200.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26207 =
          let uu____26208 =
            let uu____26221 =
              let uu____26228 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26228)  in
            let uu____26237 = elim_delayed_subst_term t2  in
            (uu____26221, uu____26237)  in
          FStar_Syntax_Syntax.Tm_let uu____26208  in
        mk1 uu____26207
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26270 =
          let uu____26271 =
            let uu____26288 = elim_delayed_subst_term t2  in
            (uv, uu____26288)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26271  in
        mk1 uu____26270
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26306 =
          let uu____26307 =
            let uu____26314 = elim_delayed_subst_term tm  in
            (uu____26314, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26307  in
        mk1 uu____26306
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26321 =
          let uu____26322 =
            let uu____26329 = elim_delayed_subst_term t2  in
            let uu____26330 = elim_delayed_subst_meta md  in
            (uu____26329, uu____26330)  in
          FStar_Syntax_Syntax.Tm_meta uu____26322  in
        mk1 uu____26321

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___117_26337  ->
         match uu___117_26337 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26341 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26341
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
        let uu____26364 =
          let uu____26365 =
            let uu____26374 = elim_delayed_subst_term t  in
            (uu____26374, uopt)  in
          FStar_Syntax_Syntax.Total uu____26365  in
        mk1 uu____26364
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26387 =
          let uu____26388 =
            let uu____26397 = elim_delayed_subst_term t  in
            (uu____26397, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26388  in
        mk1 uu____26387
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___234_26402 = ct  in
          let uu____26403 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26406 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26415 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___234_26402.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___234_26402.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26403;
            FStar_Syntax_Syntax.effect_args = uu____26406;
            FStar_Syntax_Syntax.flags = uu____26415
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___118_26418  ->
    match uu___118_26418 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26430 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26430
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26463 =
          let uu____26470 = elim_delayed_subst_term t  in (m, uu____26470)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26463
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26478 =
          let uu____26487 = elim_delayed_subst_term t  in
          (m1, m2, uu____26487)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26478
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26510  ->
         match uu____26510 with
         | (t,q) ->
             let uu____26521 = elim_delayed_subst_term t  in (uu____26521, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26541  ->
         match uu____26541 with
         | (x,q) ->
             let uu____26552 =
               let uu___235_26553 = x  in
               let uu____26554 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___235_26553.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___235_26553.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26554
               }  in
             (uu____26552, q)) bs

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
            | (uu____26638,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26644,FStar_Util.Inl t) ->
                let uu____26650 =
                  let uu____26657 =
                    let uu____26658 =
                      let uu____26671 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26671)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26658  in
                  FStar_Syntax_Syntax.mk uu____26657  in
                uu____26650 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26675 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26675 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26703 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26758 ->
                    let uu____26759 =
                      let uu____26768 =
                        let uu____26769 = FStar_Syntax_Subst.compress t4  in
                        uu____26769.FStar_Syntax_Syntax.n  in
                      (uu____26768, tc)  in
                    (match uu____26759 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26794) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26831) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26870,FStar_Util.Inl uu____26871) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26894 -> failwith "Impossible")
                 in
              (match uu____26703 with
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
          let uu____27007 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____27007 with
          | (univ_names1,binders1,tc) ->
              let uu____27065 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____27065)
  
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
          let uu____27108 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____27108 with
          | (univ_names1,binders1,tc) ->
              let uu____27168 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27168)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27205 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27205 with
           | (univ_names1,binders1,typ1) ->
               let uu___236_27233 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___236_27233.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___236_27233.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___236_27233.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___236_27233.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___237_27254 = s  in
          let uu____27255 =
            let uu____27256 =
              let uu____27265 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27265, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27256  in
          {
            FStar_Syntax_Syntax.sigel = uu____27255;
            FStar_Syntax_Syntax.sigrng =
              (uu___237_27254.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___237_27254.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___237_27254.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___237_27254.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27282 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27282 with
           | (univ_names1,uu____27300,typ1) ->
               let uu___238_27314 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_27314.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_27314.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_27314.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_27314.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27320 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27320 with
           | (univ_names1,uu____27338,typ1) ->
               let uu___239_27352 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___239_27352.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___239_27352.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___239_27352.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___239_27352.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27386 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27386 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27411 =
                            let uu____27412 =
                              let uu____27413 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27413  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27412
                             in
                          elim_delayed_subst_term uu____27411  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___240_27416 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___240_27416.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___240_27416.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___240_27416.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___240_27416.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___241_27417 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___241_27417.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_27417.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_27417.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_27417.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___242_27429 = s  in
          let uu____27430 =
            let uu____27431 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27431  in
          {
            FStar_Syntax_Syntax.sigel = uu____27430;
            FStar_Syntax_Syntax.sigrng =
              (uu___242_27429.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___242_27429.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___242_27429.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___242_27429.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27435 = elim_uvars_aux_t env us [] t  in
          (match uu____27435 with
           | (us1,uu____27453,t1) ->
               let uu___243_27467 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_27467.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_27467.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_27467.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_27467.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27468 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27470 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27470 with
           | (univs1,binders,signature) ->
               let uu____27498 =
                 let uu____27507 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27507 with
                 | (univs_opening,univs2) ->
                     let uu____27534 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27534)
                  in
               (match uu____27498 with
                | (univs_opening,univs_closing) ->
                    let uu____27551 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27557 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27558 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27557, uu____27558)  in
                    (match uu____27551 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27582 =
                           match uu____27582 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27600 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27600 with
                                | (us1,t1) ->
                                    let uu____27611 =
                                      let uu____27616 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27623 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27616, uu____27623)  in
                                    (match uu____27611 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27636 =
                                           let uu____27641 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27650 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27641, uu____27650)  in
                                         (match uu____27636 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27666 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27666
                                                 in
                                              let uu____27667 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27667 with
                                               | (uu____27688,uu____27689,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27704 =
                                                       let uu____27705 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27705
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27704
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27712 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27712 with
                           | (uu____27725,uu____27726,t1) -> t1  in
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
                             | uu____27788 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27807 =
                               let uu____27808 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27808.FStar_Syntax_Syntax.n  in
                             match uu____27807 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27867 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27898 =
                               let uu____27899 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27899.FStar_Syntax_Syntax.n  in
                             match uu____27898 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27920) ->
                                 let uu____27941 = destruct_action_body body
                                    in
                                 (match uu____27941 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27986 ->
                                 let uu____27987 = destruct_action_body t  in
                                 (match uu____27987 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____28036 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____28036 with
                           | (action_univs,t) ->
                               let uu____28045 = destruct_action_typ_templ t
                                  in
                               (match uu____28045 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___244_28086 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___244_28086.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___244_28086.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___245_28088 = ed  in
                           let uu____28089 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____28090 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____28091 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____28092 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____28093 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____28094 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____28095 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____28096 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____28097 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____28098 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____28099 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____28100 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____28101 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____28102 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___245_28088.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___245_28088.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____28089;
                             FStar_Syntax_Syntax.bind_wp = uu____28090;
                             FStar_Syntax_Syntax.if_then_else = uu____28091;
                             FStar_Syntax_Syntax.ite_wp = uu____28092;
                             FStar_Syntax_Syntax.stronger = uu____28093;
                             FStar_Syntax_Syntax.close_wp = uu____28094;
                             FStar_Syntax_Syntax.assert_p = uu____28095;
                             FStar_Syntax_Syntax.assume_p = uu____28096;
                             FStar_Syntax_Syntax.null_wp = uu____28097;
                             FStar_Syntax_Syntax.trivial = uu____28098;
                             FStar_Syntax_Syntax.repr = uu____28099;
                             FStar_Syntax_Syntax.return_repr = uu____28100;
                             FStar_Syntax_Syntax.bind_repr = uu____28101;
                             FStar_Syntax_Syntax.actions = uu____28102;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___245_28088.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___246_28105 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___246_28105.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___246_28105.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___246_28105.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___246_28105.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___119_28124 =
            match uu___119_28124 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28151 = elim_uvars_aux_t env us [] t  in
                (match uu____28151 with
                 | (us1,uu____28175,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___247_28194 = sub_eff  in
            let uu____28195 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28198 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___247_28194.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___247_28194.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28195;
              FStar_Syntax_Syntax.lift = uu____28198
            }  in
          let uu___248_28201 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___248_28201.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___248_28201.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___248_28201.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___248_28201.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28211 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28211 with
           | (univ_names1,binders1,comp1) ->
               let uu___249_28245 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___249_28245.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___249_28245.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___249_28245.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___249_28245.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28256 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28257 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  