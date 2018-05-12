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
      fun uu___102_269  ->
        match uu___102_269 with
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
      let add_opt x uu___103_1503 =
        match uu___103_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___122_1523 = fs  in
          {
            beta = true;
            iota = (uu___122_1523.iota);
            zeta = (uu___122_1523.zeta);
            weak = (uu___122_1523.weak);
            hnf = (uu___122_1523.hnf);
            primops = (uu___122_1523.primops);
            do_not_unfold_pure_lets = (uu___122_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___122_1523.unfold_until);
            unfold_only = (uu___122_1523.unfold_only);
            unfold_fully = (uu___122_1523.unfold_fully);
            unfold_attr = (uu___122_1523.unfold_attr);
            unfold_tac = (uu___122_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___122_1523.pure_subterms_within_computations);
            simplify = (uu___122_1523.simplify);
            erase_universes = (uu___122_1523.erase_universes);
            allow_unbound_universes = (uu___122_1523.allow_unbound_universes);
            reify_ = (uu___122_1523.reify_);
            compress_uvars = (uu___122_1523.compress_uvars);
            no_full_norm = (uu___122_1523.no_full_norm);
            check_no_uvars = (uu___122_1523.check_no_uvars);
            unmeta = (uu___122_1523.unmeta);
            unascribe = (uu___122_1523.unascribe);
            in_full_norm_request = (uu___122_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___122_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___123_1524 = fs  in
          {
            beta = (uu___123_1524.beta);
            iota = true;
            zeta = (uu___123_1524.zeta);
            weak = (uu___123_1524.weak);
            hnf = (uu___123_1524.hnf);
            primops = (uu___123_1524.primops);
            do_not_unfold_pure_lets = (uu___123_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___123_1524.unfold_until);
            unfold_only = (uu___123_1524.unfold_only);
            unfold_fully = (uu___123_1524.unfold_fully);
            unfold_attr = (uu___123_1524.unfold_attr);
            unfold_tac = (uu___123_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_1524.pure_subterms_within_computations);
            simplify = (uu___123_1524.simplify);
            erase_universes = (uu___123_1524.erase_universes);
            allow_unbound_universes = (uu___123_1524.allow_unbound_universes);
            reify_ = (uu___123_1524.reify_);
            compress_uvars = (uu___123_1524.compress_uvars);
            no_full_norm = (uu___123_1524.no_full_norm);
            check_no_uvars = (uu___123_1524.check_no_uvars);
            unmeta = (uu___123_1524.unmeta);
            unascribe = (uu___123_1524.unascribe);
            in_full_norm_request = (uu___123_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___124_1525 = fs  in
          {
            beta = (uu___124_1525.beta);
            iota = (uu___124_1525.iota);
            zeta = true;
            weak = (uu___124_1525.weak);
            hnf = (uu___124_1525.hnf);
            primops = (uu___124_1525.primops);
            do_not_unfold_pure_lets = (uu___124_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___124_1525.unfold_until);
            unfold_only = (uu___124_1525.unfold_only);
            unfold_fully = (uu___124_1525.unfold_fully);
            unfold_attr = (uu___124_1525.unfold_attr);
            unfold_tac = (uu___124_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___124_1525.pure_subterms_within_computations);
            simplify = (uu___124_1525.simplify);
            erase_universes = (uu___124_1525.erase_universes);
            allow_unbound_universes = (uu___124_1525.allow_unbound_universes);
            reify_ = (uu___124_1525.reify_);
            compress_uvars = (uu___124_1525.compress_uvars);
            no_full_norm = (uu___124_1525.no_full_norm);
            check_no_uvars = (uu___124_1525.check_no_uvars);
            unmeta = (uu___124_1525.unmeta);
            unascribe = (uu___124_1525.unascribe);
            in_full_norm_request = (uu___124_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___124_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___125_1526 = fs  in
          {
            beta = false;
            iota = (uu___125_1526.iota);
            zeta = (uu___125_1526.zeta);
            weak = (uu___125_1526.weak);
            hnf = (uu___125_1526.hnf);
            primops = (uu___125_1526.primops);
            do_not_unfold_pure_lets = (uu___125_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___125_1526.unfold_until);
            unfold_only = (uu___125_1526.unfold_only);
            unfold_fully = (uu___125_1526.unfold_fully);
            unfold_attr = (uu___125_1526.unfold_attr);
            unfold_tac = (uu___125_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___125_1526.pure_subterms_within_computations);
            simplify = (uu___125_1526.simplify);
            erase_universes = (uu___125_1526.erase_universes);
            allow_unbound_universes = (uu___125_1526.allow_unbound_universes);
            reify_ = (uu___125_1526.reify_);
            compress_uvars = (uu___125_1526.compress_uvars);
            no_full_norm = (uu___125_1526.no_full_norm);
            check_no_uvars = (uu___125_1526.check_no_uvars);
            unmeta = (uu___125_1526.unmeta);
            unascribe = (uu___125_1526.unascribe);
            in_full_norm_request = (uu___125_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___125_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___126_1527 = fs  in
          {
            beta = (uu___126_1527.beta);
            iota = false;
            zeta = (uu___126_1527.zeta);
            weak = (uu___126_1527.weak);
            hnf = (uu___126_1527.hnf);
            primops = (uu___126_1527.primops);
            do_not_unfold_pure_lets = (uu___126_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1527.unfold_until);
            unfold_only = (uu___126_1527.unfold_only);
            unfold_fully = (uu___126_1527.unfold_fully);
            unfold_attr = (uu___126_1527.unfold_attr);
            unfold_tac = (uu___126_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1527.pure_subterms_within_computations);
            simplify = (uu___126_1527.simplify);
            erase_universes = (uu___126_1527.erase_universes);
            allow_unbound_universes = (uu___126_1527.allow_unbound_universes);
            reify_ = (uu___126_1527.reify_);
            compress_uvars = (uu___126_1527.compress_uvars);
            no_full_norm = (uu___126_1527.no_full_norm);
            check_no_uvars = (uu___126_1527.check_no_uvars);
            unmeta = (uu___126_1527.unmeta);
            unascribe = (uu___126_1527.unascribe);
            in_full_norm_request = (uu___126_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___127_1528 = fs  in
          {
            beta = (uu___127_1528.beta);
            iota = (uu___127_1528.iota);
            zeta = false;
            weak = (uu___127_1528.weak);
            hnf = (uu___127_1528.hnf);
            primops = (uu___127_1528.primops);
            do_not_unfold_pure_lets = (uu___127_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___127_1528.unfold_until);
            unfold_only = (uu___127_1528.unfold_only);
            unfold_fully = (uu___127_1528.unfold_fully);
            unfold_attr = (uu___127_1528.unfold_attr);
            unfold_tac = (uu___127_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___127_1528.pure_subterms_within_computations);
            simplify = (uu___127_1528.simplify);
            erase_universes = (uu___127_1528.erase_universes);
            allow_unbound_universes = (uu___127_1528.allow_unbound_universes);
            reify_ = (uu___127_1528.reify_);
            compress_uvars = (uu___127_1528.compress_uvars);
            no_full_norm = (uu___127_1528.no_full_norm);
            check_no_uvars = (uu___127_1528.check_no_uvars);
            unmeta = (uu___127_1528.unmeta);
            unascribe = (uu___127_1528.unascribe);
            in_full_norm_request = (uu___127_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___127_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___128_1530 = fs  in
          {
            beta = (uu___128_1530.beta);
            iota = (uu___128_1530.iota);
            zeta = (uu___128_1530.zeta);
            weak = true;
            hnf = (uu___128_1530.hnf);
            primops = (uu___128_1530.primops);
            do_not_unfold_pure_lets = (uu___128_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___128_1530.unfold_until);
            unfold_only = (uu___128_1530.unfold_only);
            unfold_fully = (uu___128_1530.unfold_fully);
            unfold_attr = (uu___128_1530.unfold_attr);
            unfold_tac = (uu___128_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_1530.pure_subterms_within_computations);
            simplify = (uu___128_1530.simplify);
            erase_universes = (uu___128_1530.erase_universes);
            allow_unbound_universes = (uu___128_1530.allow_unbound_universes);
            reify_ = (uu___128_1530.reify_);
            compress_uvars = (uu___128_1530.compress_uvars);
            no_full_norm = (uu___128_1530.no_full_norm);
            check_no_uvars = (uu___128_1530.check_no_uvars);
            unmeta = (uu___128_1530.unmeta);
            unascribe = (uu___128_1530.unascribe);
            in_full_norm_request = (uu___128_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___129_1531 = fs  in
          {
            beta = (uu___129_1531.beta);
            iota = (uu___129_1531.iota);
            zeta = (uu___129_1531.zeta);
            weak = (uu___129_1531.weak);
            hnf = true;
            primops = (uu___129_1531.primops);
            do_not_unfold_pure_lets = (uu___129_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___129_1531.unfold_until);
            unfold_only = (uu___129_1531.unfold_only);
            unfold_fully = (uu___129_1531.unfold_fully);
            unfold_attr = (uu___129_1531.unfold_attr);
            unfold_tac = (uu___129_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1531.pure_subterms_within_computations);
            simplify = (uu___129_1531.simplify);
            erase_universes = (uu___129_1531.erase_universes);
            allow_unbound_universes = (uu___129_1531.allow_unbound_universes);
            reify_ = (uu___129_1531.reify_);
            compress_uvars = (uu___129_1531.compress_uvars);
            no_full_norm = (uu___129_1531.no_full_norm);
            check_no_uvars = (uu___129_1531.check_no_uvars);
            unmeta = (uu___129_1531.unmeta);
            unascribe = (uu___129_1531.unascribe);
            in_full_norm_request = (uu___129_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___130_1532 = fs  in
          {
            beta = (uu___130_1532.beta);
            iota = (uu___130_1532.iota);
            zeta = (uu___130_1532.zeta);
            weak = (uu___130_1532.weak);
            hnf = (uu___130_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___130_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___130_1532.unfold_until);
            unfold_only = (uu___130_1532.unfold_only);
            unfold_fully = (uu___130_1532.unfold_fully);
            unfold_attr = (uu___130_1532.unfold_attr);
            unfold_tac = (uu___130_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___130_1532.pure_subterms_within_computations);
            simplify = (uu___130_1532.simplify);
            erase_universes = (uu___130_1532.erase_universes);
            allow_unbound_universes = (uu___130_1532.allow_unbound_universes);
            reify_ = (uu___130_1532.reify_);
            compress_uvars = (uu___130_1532.compress_uvars);
            no_full_norm = (uu___130_1532.no_full_norm);
            check_no_uvars = (uu___130_1532.check_no_uvars);
            unmeta = (uu___130_1532.unmeta);
            unascribe = (uu___130_1532.unascribe);
            in_full_norm_request = (uu___130_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___130_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___131_1533 = fs  in
          {
            beta = (uu___131_1533.beta);
            iota = (uu___131_1533.iota);
            zeta = (uu___131_1533.zeta);
            weak = (uu___131_1533.weak);
            hnf = (uu___131_1533.hnf);
            primops = (uu___131_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___131_1533.unfold_until);
            unfold_only = (uu___131_1533.unfold_only);
            unfold_fully = (uu___131_1533.unfold_fully);
            unfold_attr = (uu___131_1533.unfold_attr);
            unfold_tac = (uu___131_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_1533.pure_subterms_within_computations);
            simplify = (uu___131_1533.simplify);
            erase_universes = (uu___131_1533.erase_universes);
            allow_unbound_universes = (uu___131_1533.allow_unbound_universes);
            reify_ = (uu___131_1533.reify_);
            compress_uvars = (uu___131_1533.compress_uvars);
            no_full_norm = (uu___131_1533.no_full_norm);
            check_no_uvars = (uu___131_1533.check_no_uvars);
            unmeta = (uu___131_1533.unmeta);
            unascribe = (uu___131_1533.unascribe);
            in_full_norm_request = (uu___131_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___132_1535 = fs  in
          {
            beta = (uu___132_1535.beta);
            iota = (uu___132_1535.iota);
            zeta = (uu___132_1535.zeta);
            weak = (uu___132_1535.weak);
            hnf = (uu___132_1535.hnf);
            primops = (uu___132_1535.primops);
            do_not_unfold_pure_lets = (uu___132_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___132_1535.unfold_only);
            unfold_fully = (uu___132_1535.unfold_fully);
            unfold_attr = (uu___132_1535.unfold_attr);
            unfold_tac = (uu___132_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_1535.pure_subterms_within_computations);
            simplify = (uu___132_1535.simplify);
            erase_universes = (uu___132_1535.erase_universes);
            allow_unbound_universes = (uu___132_1535.allow_unbound_universes);
            reify_ = (uu___132_1535.reify_);
            compress_uvars = (uu___132_1535.compress_uvars);
            no_full_norm = (uu___132_1535.no_full_norm);
            check_no_uvars = (uu___132_1535.check_no_uvars);
            unmeta = (uu___132_1535.unmeta);
            unascribe = (uu___132_1535.unascribe);
            in_full_norm_request = (uu___132_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___133_1539 = fs  in
          {
            beta = (uu___133_1539.beta);
            iota = (uu___133_1539.iota);
            zeta = (uu___133_1539.zeta);
            weak = (uu___133_1539.weak);
            hnf = (uu___133_1539.hnf);
            primops = (uu___133_1539.primops);
            do_not_unfold_pure_lets = (uu___133_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___133_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___133_1539.unfold_fully);
            unfold_attr = (uu___133_1539.unfold_attr);
            unfold_tac = (uu___133_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_1539.pure_subterms_within_computations);
            simplify = (uu___133_1539.simplify);
            erase_universes = (uu___133_1539.erase_universes);
            allow_unbound_universes = (uu___133_1539.allow_unbound_universes);
            reify_ = (uu___133_1539.reify_);
            compress_uvars = (uu___133_1539.compress_uvars);
            no_full_norm = (uu___133_1539.no_full_norm);
            check_no_uvars = (uu___133_1539.check_no_uvars);
            unmeta = (uu___133_1539.unmeta);
            unascribe = (uu___133_1539.unascribe);
            in_full_norm_request = (uu___133_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___134_1545 = fs  in
          {
            beta = (uu___134_1545.beta);
            iota = (uu___134_1545.iota);
            zeta = (uu___134_1545.zeta);
            weak = (uu___134_1545.weak);
            hnf = (uu___134_1545.hnf);
            primops = (uu___134_1545.primops);
            do_not_unfold_pure_lets = (uu___134_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___134_1545.unfold_until);
            unfold_only = (uu___134_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___134_1545.unfold_attr);
            unfold_tac = (uu___134_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_1545.pure_subterms_within_computations);
            simplify = (uu___134_1545.simplify);
            erase_universes = (uu___134_1545.erase_universes);
            allow_unbound_universes = (uu___134_1545.allow_unbound_universes);
            reify_ = (uu___134_1545.reify_);
            compress_uvars = (uu___134_1545.compress_uvars);
            no_full_norm = (uu___134_1545.no_full_norm);
            check_no_uvars = (uu___134_1545.check_no_uvars);
            unmeta = (uu___134_1545.unmeta);
            unascribe = (uu___134_1545.unascribe);
            in_full_norm_request = (uu___134_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___135_1549 = fs  in
          {
            beta = (uu___135_1549.beta);
            iota = (uu___135_1549.iota);
            zeta = (uu___135_1549.zeta);
            weak = (uu___135_1549.weak);
            hnf = (uu___135_1549.hnf);
            primops = (uu___135_1549.primops);
            do_not_unfold_pure_lets = (uu___135_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___135_1549.unfold_until);
            unfold_only = (uu___135_1549.unfold_only);
            unfold_fully = (uu___135_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___135_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___135_1549.pure_subterms_within_computations);
            simplify = (uu___135_1549.simplify);
            erase_universes = (uu___135_1549.erase_universes);
            allow_unbound_universes = (uu___135_1549.allow_unbound_universes);
            reify_ = (uu___135_1549.reify_);
            compress_uvars = (uu___135_1549.compress_uvars);
            no_full_norm = (uu___135_1549.no_full_norm);
            check_no_uvars = (uu___135_1549.check_no_uvars);
            unmeta = (uu___135_1549.unmeta);
            unascribe = (uu___135_1549.unascribe);
            in_full_norm_request = (uu___135_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___135_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___136_1550 = fs  in
          {
            beta = (uu___136_1550.beta);
            iota = (uu___136_1550.iota);
            zeta = (uu___136_1550.zeta);
            weak = (uu___136_1550.weak);
            hnf = (uu___136_1550.hnf);
            primops = (uu___136_1550.primops);
            do_not_unfold_pure_lets = (uu___136_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___136_1550.unfold_until);
            unfold_only = (uu___136_1550.unfold_only);
            unfold_fully = (uu___136_1550.unfold_fully);
            unfold_attr = (uu___136_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___136_1550.pure_subterms_within_computations);
            simplify = (uu___136_1550.simplify);
            erase_universes = (uu___136_1550.erase_universes);
            allow_unbound_universes = (uu___136_1550.allow_unbound_universes);
            reify_ = (uu___136_1550.reify_);
            compress_uvars = (uu___136_1550.compress_uvars);
            no_full_norm = (uu___136_1550.no_full_norm);
            check_no_uvars = (uu___136_1550.check_no_uvars);
            unmeta = (uu___136_1550.unmeta);
            unascribe = (uu___136_1550.unascribe);
            in_full_norm_request = (uu___136_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___137_1551 = fs  in
          {
            beta = (uu___137_1551.beta);
            iota = (uu___137_1551.iota);
            zeta = (uu___137_1551.zeta);
            weak = (uu___137_1551.weak);
            hnf = (uu___137_1551.hnf);
            primops = (uu___137_1551.primops);
            do_not_unfold_pure_lets = (uu___137_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___137_1551.unfold_until);
            unfold_only = (uu___137_1551.unfold_only);
            unfold_fully = (uu___137_1551.unfold_fully);
            unfold_attr = (uu___137_1551.unfold_attr);
            unfold_tac = (uu___137_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___137_1551.simplify);
            erase_universes = (uu___137_1551.erase_universes);
            allow_unbound_universes = (uu___137_1551.allow_unbound_universes);
            reify_ = (uu___137_1551.reify_);
            compress_uvars = (uu___137_1551.compress_uvars);
            no_full_norm = (uu___137_1551.no_full_norm);
            check_no_uvars = (uu___137_1551.check_no_uvars);
            unmeta = (uu___137_1551.unmeta);
            unascribe = (uu___137_1551.unascribe);
            in_full_norm_request = (uu___137_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___138_1552 = fs  in
          {
            beta = (uu___138_1552.beta);
            iota = (uu___138_1552.iota);
            zeta = (uu___138_1552.zeta);
            weak = (uu___138_1552.weak);
            hnf = (uu___138_1552.hnf);
            primops = (uu___138_1552.primops);
            do_not_unfold_pure_lets = (uu___138_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___138_1552.unfold_until);
            unfold_only = (uu___138_1552.unfold_only);
            unfold_fully = (uu___138_1552.unfold_fully);
            unfold_attr = (uu___138_1552.unfold_attr);
            unfold_tac = (uu___138_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___138_1552.erase_universes);
            allow_unbound_universes = (uu___138_1552.allow_unbound_universes);
            reify_ = (uu___138_1552.reify_);
            compress_uvars = (uu___138_1552.compress_uvars);
            no_full_norm = (uu___138_1552.no_full_norm);
            check_no_uvars = (uu___138_1552.check_no_uvars);
            unmeta = (uu___138_1552.unmeta);
            unascribe = (uu___138_1552.unascribe);
            in_full_norm_request = (uu___138_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___139_1553 = fs  in
          {
            beta = (uu___139_1553.beta);
            iota = (uu___139_1553.iota);
            zeta = (uu___139_1553.zeta);
            weak = (uu___139_1553.weak);
            hnf = (uu___139_1553.hnf);
            primops = (uu___139_1553.primops);
            do_not_unfold_pure_lets = (uu___139_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___139_1553.unfold_until);
            unfold_only = (uu___139_1553.unfold_only);
            unfold_fully = (uu___139_1553.unfold_fully);
            unfold_attr = (uu___139_1553.unfold_attr);
            unfold_tac = (uu___139_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___139_1553.pure_subterms_within_computations);
            simplify = (uu___139_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___139_1553.allow_unbound_universes);
            reify_ = (uu___139_1553.reify_);
            compress_uvars = (uu___139_1553.compress_uvars);
            no_full_norm = (uu___139_1553.no_full_norm);
            check_no_uvars = (uu___139_1553.check_no_uvars);
            unmeta = (uu___139_1553.unmeta);
            unascribe = (uu___139_1553.unascribe);
            in_full_norm_request = (uu___139_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___139_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___140_1554 = fs  in
          {
            beta = (uu___140_1554.beta);
            iota = (uu___140_1554.iota);
            zeta = (uu___140_1554.zeta);
            weak = (uu___140_1554.weak);
            hnf = (uu___140_1554.hnf);
            primops = (uu___140_1554.primops);
            do_not_unfold_pure_lets = (uu___140_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___140_1554.unfold_until);
            unfold_only = (uu___140_1554.unfold_only);
            unfold_fully = (uu___140_1554.unfold_fully);
            unfold_attr = (uu___140_1554.unfold_attr);
            unfold_tac = (uu___140_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___140_1554.pure_subterms_within_computations);
            simplify = (uu___140_1554.simplify);
            erase_universes = (uu___140_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___140_1554.reify_);
            compress_uvars = (uu___140_1554.compress_uvars);
            no_full_norm = (uu___140_1554.no_full_norm);
            check_no_uvars = (uu___140_1554.check_no_uvars);
            unmeta = (uu___140_1554.unmeta);
            unascribe = (uu___140_1554.unascribe);
            in_full_norm_request = (uu___140_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___141_1555 = fs  in
          {
            beta = (uu___141_1555.beta);
            iota = (uu___141_1555.iota);
            zeta = (uu___141_1555.zeta);
            weak = (uu___141_1555.weak);
            hnf = (uu___141_1555.hnf);
            primops = (uu___141_1555.primops);
            do_not_unfold_pure_lets = (uu___141_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___141_1555.unfold_until);
            unfold_only = (uu___141_1555.unfold_only);
            unfold_fully = (uu___141_1555.unfold_fully);
            unfold_attr = (uu___141_1555.unfold_attr);
            unfold_tac = (uu___141_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___141_1555.pure_subterms_within_computations);
            simplify = (uu___141_1555.simplify);
            erase_universes = (uu___141_1555.erase_universes);
            allow_unbound_universes = (uu___141_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___141_1555.compress_uvars);
            no_full_norm = (uu___141_1555.no_full_norm);
            check_no_uvars = (uu___141_1555.check_no_uvars);
            unmeta = (uu___141_1555.unmeta);
            unascribe = (uu___141_1555.unascribe);
            in_full_norm_request = (uu___141_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___142_1556 = fs  in
          {
            beta = (uu___142_1556.beta);
            iota = (uu___142_1556.iota);
            zeta = (uu___142_1556.zeta);
            weak = (uu___142_1556.weak);
            hnf = (uu___142_1556.hnf);
            primops = (uu___142_1556.primops);
            do_not_unfold_pure_lets = (uu___142_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1556.unfold_until);
            unfold_only = (uu___142_1556.unfold_only);
            unfold_fully = (uu___142_1556.unfold_fully);
            unfold_attr = (uu___142_1556.unfold_attr);
            unfold_tac = (uu___142_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1556.pure_subterms_within_computations);
            simplify = (uu___142_1556.simplify);
            erase_universes = (uu___142_1556.erase_universes);
            allow_unbound_universes = (uu___142_1556.allow_unbound_universes);
            reify_ = (uu___142_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___142_1556.no_full_norm);
            check_no_uvars = (uu___142_1556.check_no_uvars);
            unmeta = (uu___142_1556.unmeta);
            unascribe = (uu___142_1556.unascribe);
            in_full_norm_request = (uu___142_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___143_1557 = fs  in
          {
            beta = (uu___143_1557.beta);
            iota = (uu___143_1557.iota);
            zeta = (uu___143_1557.zeta);
            weak = (uu___143_1557.weak);
            hnf = (uu___143_1557.hnf);
            primops = (uu___143_1557.primops);
            do_not_unfold_pure_lets = (uu___143_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___143_1557.unfold_until);
            unfold_only = (uu___143_1557.unfold_only);
            unfold_fully = (uu___143_1557.unfold_fully);
            unfold_attr = (uu___143_1557.unfold_attr);
            unfold_tac = (uu___143_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___143_1557.pure_subterms_within_computations);
            simplify = (uu___143_1557.simplify);
            erase_universes = (uu___143_1557.erase_universes);
            allow_unbound_universes = (uu___143_1557.allow_unbound_universes);
            reify_ = (uu___143_1557.reify_);
            compress_uvars = (uu___143_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___143_1557.check_no_uvars);
            unmeta = (uu___143_1557.unmeta);
            unascribe = (uu___143_1557.unascribe);
            in_full_norm_request = (uu___143_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___143_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___144_1558 = fs  in
          {
            beta = (uu___144_1558.beta);
            iota = (uu___144_1558.iota);
            zeta = (uu___144_1558.zeta);
            weak = (uu___144_1558.weak);
            hnf = (uu___144_1558.hnf);
            primops = (uu___144_1558.primops);
            do_not_unfold_pure_lets = (uu___144_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___144_1558.unfold_until);
            unfold_only = (uu___144_1558.unfold_only);
            unfold_fully = (uu___144_1558.unfold_fully);
            unfold_attr = (uu___144_1558.unfold_attr);
            unfold_tac = (uu___144_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_1558.pure_subterms_within_computations);
            simplify = (uu___144_1558.simplify);
            erase_universes = (uu___144_1558.erase_universes);
            allow_unbound_universes = (uu___144_1558.allow_unbound_universes);
            reify_ = (uu___144_1558.reify_);
            compress_uvars = (uu___144_1558.compress_uvars);
            no_full_norm = (uu___144_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___144_1558.unmeta);
            unascribe = (uu___144_1558.unascribe);
            in_full_norm_request = (uu___144_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___145_1559 = fs  in
          {
            beta = (uu___145_1559.beta);
            iota = (uu___145_1559.iota);
            zeta = (uu___145_1559.zeta);
            weak = (uu___145_1559.weak);
            hnf = (uu___145_1559.hnf);
            primops = (uu___145_1559.primops);
            do_not_unfold_pure_lets = (uu___145_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___145_1559.unfold_until);
            unfold_only = (uu___145_1559.unfold_only);
            unfold_fully = (uu___145_1559.unfold_fully);
            unfold_attr = (uu___145_1559.unfold_attr);
            unfold_tac = (uu___145_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___145_1559.pure_subterms_within_computations);
            simplify = (uu___145_1559.simplify);
            erase_universes = (uu___145_1559.erase_universes);
            allow_unbound_universes = (uu___145_1559.allow_unbound_universes);
            reify_ = (uu___145_1559.reify_);
            compress_uvars = (uu___145_1559.compress_uvars);
            no_full_norm = (uu___145_1559.no_full_norm);
            check_no_uvars = (uu___145_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___145_1559.unascribe);
            in_full_norm_request = (uu___145_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___145_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___146_1560 = fs  in
          {
            beta = (uu___146_1560.beta);
            iota = (uu___146_1560.iota);
            zeta = (uu___146_1560.zeta);
            weak = (uu___146_1560.weak);
            hnf = (uu___146_1560.hnf);
            primops = (uu___146_1560.primops);
            do_not_unfold_pure_lets = (uu___146_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___146_1560.unfold_until);
            unfold_only = (uu___146_1560.unfold_only);
            unfold_fully = (uu___146_1560.unfold_fully);
            unfold_attr = (uu___146_1560.unfold_attr);
            unfold_tac = (uu___146_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_1560.pure_subterms_within_computations);
            simplify = (uu___146_1560.simplify);
            erase_universes = (uu___146_1560.erase_universes);
            allow_unbound_universes = (uu___146_1560.allow_unbound_universes);
            reify_ = (uu___146_1560.reify_);
            compress_uvars = (uu___146_1560.compress_uvars);
            no_full_norm = (uu___146_1560.no_full_norm);
            check_no_uvars = (uu___146_1560.check_no_uvars);
            unmeta = (uu___146_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___146_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_1560.weakly_reduce_scrutinee)
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
  fun uu___104_3245  ->
    match uu___104_3245 with
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
  fun uu___105_3307  ->
    match uu___105_3307 with
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
  fun uu___106_3443  ->
    match uu___106_3443 with | [] -> true | uu____3446 -> false
  
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
                                      (fun uu___107_4052  ->
                                         match uu___107_4052 with
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
                                                 (let uu___151_4076 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___151_4076.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___151_4076.FStar_Syntax_Syntax.sort)
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
                         let uu___152_4088 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___152_4088.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___152_4088.FStar_Syntax_Syntax.vars)
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
                           let uu___153_4133 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___153_4133.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___153_4133.FStar_Syntax_Syntax.index);
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
                           let uu____4541 =
                             let uu____4542 =
                               let uu____4549 =
                                 let uu____4550 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4550
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4549, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4542  in
                           mk uu____4541 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4641 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4641
                      | FStar_Util.Inr c ->
                          let uu____4655 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4655
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4674 =
                        let uu____4675 =
                          let uu____4702 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4702, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4675  in
                      mk uu____4674 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4748 =
                            let uu____4749 =
                              let uu____4756 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4756, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4749  in
                          mk uu____4748 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4808  -> dummy :: env1) env
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
                    let uu____4829 =
                      let uu____4840 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4840
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4859 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___154_4875 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_4875.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_4875.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4859))
                       in
                    (match uu____4829 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___155_4893 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_4893.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_4893.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___155_4893.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___155_4893.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4907,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4970  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4987 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4987
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4999  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5023 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5023
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___156_5031 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___156_5031.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___156_5031.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___157_5032 = lb  in
                      let uu____5033 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___157_5032.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___157_5032.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5033;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___157_5032.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___157_5032.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5065  -> fun env1  -> dummy :: env1)
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
            (fun uu____5154  ->
               let uu____5155 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5156 = env_to_string env  in
               let uu____5157 = stack_to_string stack  in
               let uu____5158 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5155 uu____5156 uu____5157 uu____5158);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5163,uu____5164),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5241 = close_binders cfg env' bs  in
               (match uu____5241 with
                | (bs1,uu____5255) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5271 =
                      let uu___158_5274 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___158_5274.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___158_5274.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5271)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5330 =
                 match uu____5330 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5445 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5474 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5558  ->
                                     fun uu____5559  ->
                                       match (uu____5558, uu____5559) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5698 = norm_pat env4 p1
                                              in
                                           (match uu____5698 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5474 with
                            | (pats1,env4) ->
                                ((let uu___159_5860 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___159_5860.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___160_5879 = x  in
                             let uu____5880 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_5879.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_5879.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5880
                             }  in
                           ((let uu___161_5894 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___161_5894.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___162_5905 = x  in
                             let uu____5906 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_5905.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_5905.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5906
                             }  in
                           ((let uu___163_5920 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___163_5920.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___164_5936 = x  in
                             let uu____5937 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___164_5936.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___164_5936.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5937
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___165_5954 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___165_5954.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5959 = norm_pat env2 pat  in
                     (match uu____5959 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6028 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6028
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6047 =
                   let uu____6048 =
                     let uu____6071 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6071)  in
                   FStar_Syntax_Syntax.Tm_match uu____6048  in
                 mk uu____6047 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6184 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6273  ->
                                       match uu____6273 with
                                       | (a,q) ->
                                           let uu____6292 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6292, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6184
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6303 =
                       let uu____6310 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6310)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6303
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6322 =
                       let uu____6331 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6331)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6322
                 | uu____6336 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6342 -> failwith "Impossible: unexpected stack element")

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
        let uu____6356 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6429  ->
                  fun uu____6430  ->
                    match (uu____6429, uu____6430) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_6548 = b  in
                          let uu____6549 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_6548.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_6548.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6549
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6356 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6666 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6679 = inline_closure_env cfg env [] t  in
                 let uu____6680 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6679 uu____6680
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6693 = inline_closure_env cfg env [] t  in
                 let uu____6694 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6693 uu____6694
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6738  ->
                           match uu____6738 with
                           | (a,q) ->
                               let uu____6751 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6751, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___108_6766  ->
                           match uu___108_6766 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6770 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6770
                           | f -> f))
                    in
                 let uu____6774 =
                   let uu___167_6775 = c1  in
                   let uu____6776 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6776;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_6775.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6774)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___109_6786  ->
            match uu___109_6786 with
            | FStar_Syntax_Syntax.DECREASES uu____6787 -> false
            | uu____6790 -> true))

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
                   (fun uu___110_6808  ->
                      match uu___110_6808 with
                      | FStar_Syntax_Syntax.DECREASES uu____6809 -> false
                      | uu____6812 -> true))
               in
            let rc1 =
              let uu___168_6814 = rc  in
              let uu____6815 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_6814.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6815;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6824 -> lopt

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
    let uu____6929 =
      let uu____6938 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6938  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6929  in
  let arg_as_bounded_int uu____6964 =
    match uu____6964 with
    | (a,uu____6976) ->
        let uu____6983 =
          let uu____6984 = FStar_Syntax_Subst.compress a  in
          uu____6984.FStar_Syntax_Syntax.n  in
        (match uu____6983 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6994;
                FStar_Syntax_Syntax.vars = uu____6995;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6997;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6998;_},uu____6999)::[])
             when
             let uu____7038 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7038 "int_to_t" ->
             let uu____7039 =
               let uu____7044 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7044)  in
             FStar_Pervasives_Native.Some uu____7039
         | uu____7049 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7097 = f a  in FStar_Pervasives_Native.Some uu____7097
    | uu____7098 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7154 = f a0 a1  in FStar_Pervasives_Native.Some uu____7154
    | uu____7155 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7213 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7213  in
  let binary_op as_a f res args =
    let uu____7284 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7284  in
  let as_primitive_step is_strong uu____7321 =
    match uu____7321 with
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
           let uu____7381 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7381)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7417 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7417)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7446 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7446)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7482 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7482)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7518 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7518)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7650 =
          let uu____7659 = as_a a  in
          let uu____7662 = as_b b  in (uu____7659, uu____7662)  in
        (match uu____7650 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7677 =
               let uu____7678 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7678  in
             FStar_Pervasives_Native.Some uu____7677
         | uu____7679 -> FStar_Pervasives_Native.None)
    | uu____7688 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7708 =
        let uu____7709 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7709  in
      mk uu____7708 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7721 =
      let uu____7724 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7724  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7721  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7766 =
      let uu____7767 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7767  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7766
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7831 = arg_as_string a1  in
        (match uu____7831 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7837 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7837 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7850 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7850
              | uu____7851 -> FStar_Pervasives_Native.None)
         | uu____7856 -> FStar_Pervasives_Native.None)
    | uu____7859 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7879 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7879
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7916 =
          let uu____7937 = arg_as_string fn  in
          let uu____7940 = arg_as_int from_line  in
          let uu____7943 = arg_as_int from_col  in
          let uu____7946 = arg_as_int to_line  in
          let uu____7949 = arg_as_int to_col  in
          (uu____7937, uu____7940, uu____7943, uu____7946, uu____7949)  in
        (match uu____7916 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7980 =
                 let uu____7981 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7982 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7981 uu____7982  in
               let uu____7983 =
                 let uu____7984 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7985 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7984 uu____7985  in
               FStar_Range.mk_range fn1 uu____7980 uu____7983  in
             let uu____7986 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7986
         | uu____7987 -> FStar_Pervasives_Native.None)
    | uu____8008 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8041)::(a1,uu____8043)::(a2,uu____8045)::[] ->
        let uu____8082 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8082 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8087 -> FStar_Pervasives_Native.None)
    | uu____8088 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8119)::[] ->
        let uu____8128 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8128 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8134 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8134
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8135 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8161 =
      let uu____8178 =
        let uu____8195 =
          let uu____8212 =
            let uu____8229 =
              let uu____8246 =
                let uu____8263 =
                  let uu____8280 =
                    let uu____8297 =
                      let uu____8314 =
                        let uu____8331 =
                          let uu____8348 =
                            let uu____8365 =
                              let uu____8382 =
                                let uu____8399 =
                                  let uu____8416 =
                                    let uu____8433 =
                                      let uu____8450 =
                                        let uu____8467 =
                                          let uu____8484 =
                                            let uu____8501 =
                                              let uu____8518 =
                                                let uu____8533 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8533,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8542 =
                                                let uu____8559 =
                                                  let uu____8574 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8574,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8587 =
                                                  let uu____8604 =
                                                    let uu____8619 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8619,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8628 =
                                                    let uu____8645 =
                                                      let uu____8660 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8660,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8645]  in
                                                  uu____8604 :: uu____8628
                                                   in
                                                uu____8559 :: uu____8587  in
                                              uu____8518 :: uu____8542  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8501
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8484
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8467
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8450
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8433
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8880 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8880 y)))
                                    :: uu____8416
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8399
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8382
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8365
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8348
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8331
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8314
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9075 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9075)))
                      :: uu____8297
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9105 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9105)))
                    :: uu____8280
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9135 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9135)))
                  :: uu____8263
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9165 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9165)))
                :: uu____8246
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8229
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8212
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8195
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8178
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8161
     in
  let weak_ops =
    let uu____9320 =
      let uu____9335 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9335, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9320]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9415 =
        let uu____9420 =
          let uu____9421 = FStar_Syntax_Syntax.as_arg c  in [uu____9421]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9420  in
      uu____9415 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9495 =
                let uu____9510 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9510, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9532  ->
                          fun uu____9533  ->
                            match (uu____9532, uu____9533) with
                            | ((int_to_t1,x),(uu____9552,y)) ->
                                let uu____9562 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9562)))
                 in
              let uu____9563 =
                let uu____9580 =
                  let uu____9595 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9595, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9617  ->
                            fun uu____9618  ->
                              match (uu____9617, uu____9618) with
                              | ((int_to_t1,x),(uu____9637,y)) ->
                                  let uu____9647 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9647)))
                   in
                let uu____9648 =
                  let uu____9665 =
                    let uu____9680 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9680, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9702  ->
                              fun uu____9703  ->
                                match (uu____9702, uu____9703) with
                                | ((int_to_t1,x),(uu____9722,y)) ->
                                    let uu____9732 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9732)))
                     in
                  let uu____9733 =
                    let uu____9750 =
                      let uu____9765 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9765, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9783  ->
                                match uu____9783 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9750]  in
                  uu____9665 :: uu____9733  in
                uu____9580 :: uu____9648  in
              uu____9495 :: uu____9563))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9913 =
                let uu____9928 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9928, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9950  ->
                          fun uu____9951  ->
                            match (uu____9950, uu____9951) with
                            | ((int_to_t1,x),(uu____9970,y)) ->
                                let uu____9980 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9980)))
                 in
              let uu____9981 =
                let uu____9998 =
                  let uu____10013 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10013, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10035  ->
                            fun uu____10036  ->
                              match (uu____10035, uu____10036) with
                              | ((int_to_t1,x),(uu____10055,y)) ->
                                  let uu____10065 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10065)))
                   in
                [uu____9998]  in
              uu____9913 :: uu____9981))
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
    | (_typ,uu____10195)::(a1,uu____10197)::(a2,uu____10199)::[] ->
        let uu____10236 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10236 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10240 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10240.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10240.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10242 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10242.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10242.FStar_Syntax_Syntax.vars)
                })
         | uu____10243 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10245)::uu____10246::(a1,uu____10248)::(a2,uu____10250)::[]
        ->
        let uu____10299 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10299 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10303 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10303.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10303.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10305 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10305.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10305.FStar_Syntax_Syntax.vars)
                })
         | uu____10306 -> FStar_Pervasives_Native.None)
    | uu____10307 -> failwith "Unexpected number of arguments"  in
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
    let uu____10361 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10361 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10413 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10413) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10475  ->
           fun subst1  ->
             match uu____10475 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10516,uu____10517)) ->
                      let uu____10576 = b  in
                      (match uu____10576 with
                       | (bv,uu____10584) ->
                           let uu____10585 =
                             let uu____10586 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10586  in
                           if uu____10585
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10591 = unembed_binder term1  in
                              match uu____10591 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10598 =
                                      let uu___171_10599 = bv  in
                                      let uu____10600 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___171_10599.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___171_10599.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10600
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10598
                                     in
                                  let b_for_x =
                                    let uu____10604 =
                                      let uu____10611 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10611)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10604  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___111_10625  ->
                                         match uu___111_10625 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10626,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10628;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10629;_})
                                             ->
                                             let uu____10634 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10634
                                         | uu____10635 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10636 -> subst1)) env []
  
let reduce_primops :
  'Auu____10659 'Auu____10660 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10659) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10660 ->
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
            (let uu____10708 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10708 with
             | (head1,args) ->
                 let uu____10747 =
                   let uu____10748 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10748.FStar_Syntax_Syntax.n  in
                 (match uu____10747 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10754 = find_prim_step cfg fv  in
                      (match uu____10754 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10780  ->
                                   let uu____10781 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10782 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10789 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10781 uu____10782 uu____10789);
                              tm)
                           else
                             (let uu____10791 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10791 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10905  ->
                                        let uu____10906 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10906);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10909  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10911 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10911 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10919  ->
                                              let uu____10920 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10920);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10926  ->
                                              let uu____10927 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10928 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10927 uu____10928);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10929 ->
                           (log_primops cfg
                              (fun uu____10933  ->
                                 let uu____10934 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10934);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10938  ->
                            let uu____10939 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10939);
                       (match args with
                        | (a1,uu____10943)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10960 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10972  ->
                            let uu____10973 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10973);
                       (match args with
                        | (t,uu____10977)::(r,uu____10979)::[] ->
                            let uu____11006 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11006 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11012 -> tm))
                  | uu____11021 -> tm))
  
let reduce_equality :
  'Auu____11032 'Auu____11033 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11032) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11033 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_11079 = cfg  in
         {
           steps =
             (let uu___173_11082 = default_steps  in
              {
                beta = (uu___173_11082.beta);
                iota = (uu___173_11082.iota);
                zeta = (uu___173_11082.zeta);
                weak = (uu___173_11082.weak);
                hnf = (uu___173_11082.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___173_11082.do_not_unfold_pure_lets);
                unfold_until = (uu___173_11082.unfold_until);
                unfold_only = (uu___173_11082.unfold_only);
                unfold_fully = (uu___173_11082.unfold_fully);
                unfold_attr = (uu___173_11082.unfold_attr);
                unfold_tac = (uu___173_11082.unfold_tac);
                pure_subterms_within_computations =
                  (uu___173_11082.pure_subterms_within_computations);
                simplify = (uu___173_11082.simplify);
                erase_universes = (uu___173_11082.erase_universes);
                allow_unbound_universes =
                  (uu___173_11082.allow_unbound_universes);
                reify_ = (uu___173_11082.reify_);
                compress_uvars = (uu___173_11082.compress_uvars);
                no_full_norm = (uu___173_11082.no_full_norm);
                check_no_uvars = (uu___173_11082.check_no_uvars);
                unmeta = (uu___173_11082.unmeta);
                unascribe = (uu___173_11082.unascribe);
                in_full_norm_request = (uu___173_11082.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___173_11082.weakly_reduce_scrutinee)
              });
           tcenv = (uu___172_11079.tcenv);
           debug = (uu___172_11079.debug);
           delta_level = (uu___172_11079.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___172_11079.strong);
           memoize_lazy = (uu___172_11079.memoize_lazy);
           normalize_pure_lets = (uu___172_11079.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11089 .
    FStar_Syntax_Syntax.term -> 'Auu____11089 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11104 =
        let uu____11111 =
          let uu____11112 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11112.FStar_Syntax_Syntax.n  in
        (uu____11111, args)  in
      match uu____11104 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11118::uu____11119::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11123::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11128::uu____11129::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11132 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___112_11145  ->
    match uu___112_11145 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11151 =
          let uu____11154 =
            let uu____11155 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11155  in
          [uu____11154]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11151
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11161 =
          let uu____11164 =
            let uu____11165 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11165  in
          [uu____11164]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11161
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11188 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11188)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11239 =
            let uu____11244 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11244 s  in
          match uu____11239 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11260 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11260
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11286::(tm,uu____11288)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11317)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11338)::uu____11339::(tm,uu____11341)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11382 =
              let uu____11387 = full_norm steps  in parse_steps uu____11387
               in
            (match uu____11382 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11426 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___113_11445  ->
    match uu___113_11445 with
    | (App
        (uu____11448,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11449;
                       FStar_Syntax_Syntax.vars = uu____11450;_},uu____11451,uu____11452))::uu____11453
        -> true
    | uu____11458 -> false
  
let firstn :
  'Auu____11467 .
    Prims.int ->
      'Auu____11467 Prims.list ->
        ('Auu____11467 Prims.list,'Auu____11467 Prims.list)
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
          (uu____11509,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11510;
                         FStar_Syntax_Syntax.vars = uu____11511;_},uu____11512,uu____11513))::uu____11514
          -> (cfg.steps).reify_
      | uu____11519 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11542) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11552) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11571  ->
                  match uu____11571 with
                  | (a,uu____11579) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11585 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11610 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11611 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11626 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11627 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11628 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11629 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11630 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11631 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11638 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11645 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11658 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11675 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11688 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11695 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11757  ->
                   match uu____11757 with
                   | (a,uu____11765) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11772) ->
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
                     (fun uu____11894  ->
                        match uu____11894 with
                        | (a,uu____11902) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11907,uu____11908,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11914,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11920 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11927 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11928 -> false))
  
let decide_unfolding :
  'Auu____11943 .
    cfg ->
      'Auu____11943 ->
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
                let uu____12029 =
                  FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                match uu____12029 with
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
                  (fun uu____12157  ->
                     fun uu____12158  ->
                       match (uu____12157, uu____12158) with
                       | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                  l (false, false, false)
                 in
              let string_of_res uu____12218 =
                match uu____12218 with
                | (x,y,z) ->
                    let uu____12228 = FStar_Util.string_of_bool x  in
                    let uu____12229 = FStar_Util.string_of_bool y  in
                    let uu____12230 = FStar_Util.string_of_bool z  in
                    FStar_Util.format3 "(%s,%s,%s)" uu____12228 uu____12229
                      uu____12230
                 in
              let res =
                match (qninfo, ((cfg.steps).unfold_only),
                        ((cfg.steps).unfold_fully),
                        ((cfg.steps).unfold_attr))
                with
                | uu____12276 when
                    FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                    let b = should_reify cfg stack  in
                    (log_unfolding cfg
                       (fun uu____12322  ->
                          let uu____12323 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          let uu____12324 = FStar_Util.string_of_bool b  in
                          FStar_Util.print2
                            ">>> For DM4F action %s, should_reify = %s\n"
                            uu____12323 uu____12324);
                     if b then reif else no)
                | uu____12332 when
                    let uu____12373 = find_prim_step cfg fv  in
                    FStar_Option.isSome uu____12373 -> no
                | (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr
                    ({
                       FStar_Syntax_Syntax.sigel =
                         FStar_Syntax_Syntax.Sig_let
                         ((is_rec,uu____12377),uu____12378);
                       FStar_Syntax_Syntax.sigrng = uu____12379;
                       FStar_Syntax_Syntax.sigquals = qs;
                       FStar_Syntax_Syntax.sigmeta = uu____12381;
                       FStar_Syntax_Syntax.sigattrs = uu____12382;_},uu____12383),uu____12384),uu____12385,uu____12386,uu____12387)
                    when
                    FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                      qs
                    -> no
                | (uu____12490,uu____12491,uu____12492,uu____12493) when
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
                         ((is_rec,uu____12559),uu____12560);
                       FStar_Syntax_Syntax.sigrng = uu____12561;
                       FStar_Syntax_Syntax.sigquals = qs;
                       FStar_Syntax_Syntax.sigmeta = uu____12563;
                       FStar_Syntax_Syntax.sigattrs = uu____12564;_},uu____12565),uu____12566),uu____12567,uu____12568,uu____12569)
                    when is_rec && (Prims.op_Negation (cfg.steps).zeta) -> no
                | (uu____12672,FStar_Pervasives_Native.Some
                   uu____12673,uu____12674,uu____12675) ->
                    (log_unfolding cfg
                       (fun uu____12743  ->
                          let uu____12744 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____12744);
                     (let uu____12745 =
                        let uu____12754 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12774 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____12774
                           in
                        let uu____12781 =
                          let uu____12790 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____12810 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____12810
                             in
                          let uu____12819 =
                            let uu____12828 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____12848 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____12848
                               in
                            [uu____12828]  in
                          uu____12790 :: uu____12819  in
                        uu____12754 :: uu____12781  in
                      comb_or uu____12745))
                | (uu____12879,uu____12880,FStar_Pervasives_Native.Some
                   uu____12881,uu____12882) ->
                    (log_unfolding cfg
                       (fun uu____12950  ->
                          let uu____12951 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____12951);
                     (let uu____12952 =
                        let uu____12961 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12981 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____12981
                           in
                        let uu____12988 =
                          let uu____12997 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____13017 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____13017
                             in
                          let uu____13026 =
                            let uu____13035 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____13055 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____13055
                               in
                            [uu____13035]  in
                          uu____12997 :: uu____13026  in
                        uu____12961 :: uu____12988  in
                      comb_or uu____12952))
                | (uu____13086,uu____13087,uu____13088,FStar_Pervasives_Native.Some
                   uu____13089) ->
                    (log_unfolding cfg
                       (fun uu____13157  ->
                          let uu____13158 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____13158);
                     (let uu____13159 =
                        let uu____13168 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____13188 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____13188
                           in
                        let uu____13195 =
                          let uu____13204 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____13224 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____13224
                             in
                          let uu____13233 =
                            let uu____13242 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____13262 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____13262
                               in
                            [uu____13242]  in
                          uu____13204 :: uu____13233  in
                        uu____13168 :: uu____13195  in
                      comb_or uu____13159))
                | uu____13293 ->
                    (log_unfolding cfg
                       (fun uu____13339  ->
                          let uu____13340 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          let uu____13341 =
                            FStar_Syntax_Print.delta_depth_to_string
                              fv.FStar_Syntax_Syntax.fv_delta
                             in
                          let uu____13342 =
                            FStar_Common.string_of_list
                              FStar_TypeChecker_Env.string_of_delta_level
                              cfg.delta_level
                             in
                          FStar_Util.print3
                            ">>> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                            uu____13340 uu____13341 uu____13342);
                     (let uu____13343 =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_Util.for_some
                             (fun uu___114_13347  ->
                                match uu___114_13347 with
                                | FStar_TypeChecker_Env.UnfoldTac  -> false
                                | FStar_TypeChecker_Env.NoDelta  -> false
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | FStar_TypeChecker_Env.Unfold l ->
                                    FStar_TypeChecker_Common.delta_depth_greater_than
                                      fv.FStar_Syntax_Syntax.fv_delta l))
                         in
                      FStar_All.pipe_left yesno uu____13343))
                 in
              log_unfolding cfg
                (fun uu____13360  ->
                   let uu____13361 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____13362 = FStar_Range.string_of_range rng  in
                   let uu____13363 = string_of_res res  in
                   FStar_Util.print3 ">>> For %s (%s), unfolding res = %s\n"
                     uu____13361 uu____13362 uu____13363);
              (match res with
               | (false ,uu____13372,uu____13373) ->
                   FStar_Pervasives_Native.None
               | (true ,false ,false ) ->
                   FStar_Pervasives_Native.Some (cfg, stack)
               | (true ,true ,false ) ->
                   let cfg' =
                     let uu___174_13389 = cfg  in
                     {
                       steps =
                         (let uu___175_13392 = cfg.steps  in
                          {
                            beta = (uu___175_13392.beta);
                            iota = false;
                            zeta = false;
                            weak = false;
                            hnf = false;
                            primops = false;
                            do_not_unfold_pure_lets =
                              (uu___175_13392.do_not_unfold_pure_lets);
                            unfold_until =
                              (FStar_Pervasives_Native.Some
                                 FStar_Syntax_Syntax.delta_constant);
                            unfold_only = FStar_Pervasives_Native.None;
                            unfold_fully = FStar_Pervasives_Native.None;
                            unfold_attr = (uu___175_13392.unfold_attr);
                            unfold_tac = (uu___175_13392.unfold_tac);
                            pure_subterms_within_computations =
                              (uu___175_13392.pure_subterms_within_computations);
                            simplify = false;
                            erase_universes =
                              (uu___175_13392.erase_universes);
                            allow_unbound_universes =
                              (uu___175_13392.allow_unbound_universes);
                            reify_ = (uu___175_13392.reify_);
                            compress_uvars = (uu___175_13392.compress_uvars);
                            no_full_norm = (uu___175_13392.no_full_norm);
                            check_no_uvars = (uu___175_13392.check_no_uvars);
                            unmeta = (uu___175_13392.unmeta);
                            unascribe = (uu___175_13392.unascribe);
                            in_full_norm_request =
                              (uu___175_13392.in_full_norm_request);
                            weakly_reduce_scrutinee =
                              (uu___175_13392.weakly_reduce_scrutinee)
                          });
                       tcenv = (uu___174_13389.tcenv);
                       debug = (uu___174_13389.debug);
                       delta_level = (uu___174_13389.delta_level);
                       primitive_steps = (uu___174_13389.primitive_steps);
                       strong = (uu___174_13389.strong);
                       memoize_lazy = (uu___174_13389.memoize_lazy);
                       normalize_pure_lets =
                         (uu___174_13389.normalize_pure_lets)
                     }  in
                   let stack' = (Cfg cfg) :: stack  in
                   FStar_Pervasives_Native.Some (cfg', stack')
               | (true ,false ,true ) ->
                   let uu____13408 =
                     let uu____13415 = FStar_List.tl stack  in
                     (cfg, uu____13415)  in
                   FStar_Pervasives_Native.Some uu____13408
               | uu____13426 ->
                   let uu____13433 =
                     let uu____13434 = string_of_res res  in
                     FStar_Util.format1 "Unexpected unfolding result: %s"
                       uu____13434
                      in
                   FStar_All.pipe_left failwith uu____13433)
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13742 ->
                   let uu____13767 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13767
               | uu____13768 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13776  ->
               let uu____13777 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13778 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13779 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13786 =
                 let uu____13787 =
                   let uu____13790 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13790
                    in
                 stack_to_string uu____13787  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13777 uu____13778 uu____13779 uu____13786);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13813 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13814 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13815 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13816;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____13817;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13820;
                 FStar_Syntax_Syntax.fv_delta = uu____13821;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13822;
                 FStar_Syntax_Syntax.fv_delta = uu____13823;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13824);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____13831 ->
               let uu____13838 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13838
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____13868 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____13868)
               ->
               let cfg' =
                 let uu___176_13870 = cfg  in
                 {
                   steps =
                     (let uu___177_13873 = cfg.steps  in
                      {
                        beta = (uu___177_13873.beta);
                        iota = (uu___177_13873.iota);
                        zeta = (uu___177_13873.zeta);
                        weak = (uu___177_13873.weak);
                        hnf = (uu___177_13873.hnf);
                        primops = (uu___177_13873.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___177_13873.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___177_13873.unfold_attr);
                        unfold_tac = (uu___177_13873.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___177_13873.pure_subterms_within_computations);
                        simplify = (uu___177_13873.simplify);
                        erase_universes = (uu___177_13873.erase_universes);
                        allow_unbound_universes =
                          (uu___177_13873.allow_unbound_universes);
                        reify_ = (uu___177_13873.reify_);
                        compress_uvars = (uu___177_13873.compress_uvars);
                        no_full_norm = (uu___177_13873.no_full_norm);
                        check_no_uvars = (uu___177_13873.check_no_uvars);
                        unmeta = (uu___177_13873.unmeta);
                        unascribe = (uu___177_13873.unascribe);
                        in_full_norm_request =
                          (uu___177_13873.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___177_13873.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___176_13870.tcenv);
                   debug = (uu___176_13870.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___176_13870.primitive_steps);
                   strong = (uu___176_13870.strong);
                   memoize_lazy = (uu___176_13870.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13878 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____13878 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____13907  ->
                              fun stack1  ->
                                match uu____13907 with
                                | (a,aq) ->
                                    let uu____13919 =
                                      let uu____13920 =
                                        let uu____13927 =
                                          let uu____13928 =
                                            let uu____13959 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____13959, false)  in
                                          Clos uu____13928  in
                                        (uu____13927, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____13920  in
                                    uu____13919 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14047  ->
                          let uu____14048 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14048);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14070 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___115_14075  ->
                                match uu___115_14075 with
                                | UnfoldUntil uu____14076 -> true
                                | UnfoldOnly uu____14077 -> true
                                | UnfoldFully uu____14080 -> true
                                | uu____14083 -> false))
                         in
                      if uu____14070
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___178_14088 = cfg  in
                      let uu____14089 =
                        let uu___179_14090 = to_fsteps s  in
                        {
                          beta = (uu___179_14090.beta);
                          iota = (uu___179_14090.iota);
                          zeta = (uu___179_14090.zeta);
                          weak = (uu___179_14090.weak);
                          hnf = (uu___179_14090.hnf);
                          primops = (uu___179_14090.primops);
                          do_not_unfold_pure_lets =
                            (uu___179_14090.do_not_unfold_pure_lets);
                          unfold_until = (uu___179_14090.unfold_until);
                          unfold_only = (uu___179_14090.unfold_only);
                          unfold_fully = (uu___179_14090.unfold_fully);
                          unfold_attr = (uu___179_14090.unfold_attr);
                          unfold_tac = (uu___179_14090.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___179_14090.pure_subterms_within_computations);
                          simplify = (uu___179_14090.simplify);
                          erase_universes = (uu___179_14090.erase_universes);
                          allow_unbound_universes =
                            (uu___179_14090.allow_unbound_universes);
                          reify_ = (uu___179_14090.reify_);
                          compress_uvars = (uu___179_14090.compress_uvars);
                          no_full_norm = (uu___179_14090.no_full_norm);
                          check_no_uvars = (uu___179_14090.check_no_uvars);
                          unmeta = (uu___179_14090.unmeta);
                          unascribe = (uu___179_14090.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___179_14090.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14089;
                        tcenv = (uu___178_14088.tcenv);
                        debug = (uu___178_14088.debug);
                        delta_level;
                        primitive_steps = (uu___178_14088.primitive_steps);
                        strong = (uu___178_14088.strong);
                        memoize_lazy = (uu___178_14088.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14099 =
                          let uu____14100 =
                            let uu____14105 = FStar_Util.now ()  in
                            (t1, uu____14105)  in
                          Debug uu____14100  in
                        uu____14099 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14109 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14109
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14118 =
                      let uu____14125 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14125, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14118  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14135 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14135  in
               let uu____14136 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14136 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14164 = lookup_bvar env x  in
               (match uu____14164 with
                | Univ uu____14165 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14214 = FStar_ST.op_Bang r  in
                      (match uu____14214 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14336  ->
                                 let uu____14337 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14338 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14337
                                   uu____14338);
                            (let uu____14339 = maybe_weakly_reduced t'  in
                             if uu____14339
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14340 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14411)::uu____14412 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14422,uu____14423))::stack_rest ->
                    (match c with
                     | Univ uu____14427 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14436 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14457  ->
                                    let uu____14458 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14458);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14486  ->
                                    let uu____14487 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14487);
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
                       (fun uu____14553  ->
                          let uu____14554 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14554);
                     norm cfg env stack1 t1)
                | (Match uu____14555)::uu____14556 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14570 = cfg.steps  in
                             {
                               beta = (uu___180_14570.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14570.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14570.unfold_until);
                               unfold_only = (uu___180_14570.unfold_only);
                               unfold_fully = (uu___180_14570.unfold_fully);
                               unfold_attr = (uu___180_14570.unfold_attr);
                               unfold_tac = (uu___180_14570.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14570.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14570.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14570.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14570.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14570.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14570.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14572 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14572.tcenv);
                               debug = (uu___181_14572.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14572.primitive_steps);
                               strong = (uu___181_14572.strong);
                               memoize_lazy = (uu___181_14572.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14572.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14574 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14574 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14606  -> dummy :: env1) env)
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
                                          let uu____14647 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14647)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14652 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14652.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14652.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14653 -> lopt  in
                           (log cfg
                              (fun uu____14659  ->
                                 let uu____14660 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14660);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14669 = cfg  in
                               {
                                 steps = (uu___183_14669.steps);
                                 tcenv = (uu___183_14669.tcenv);
                                 debug = (uu___183_14669.debug);
                                 delta_level = (uu___183_14669.delta_level);
                                 primitive_steps =
                                   (uu___183_14669.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14669.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14669.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____14672)::uu____14673 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14683 = cfg.steps  in
                             {
                               beta = (uu___180_14683.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14683.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14683.unfold_until);
                               unfold_only = (uu___180_14683.unfold_only);
                               unfold_fully = (uu___180_14683.unfold_fully);
                               unfold_attr = (uu___180_14683.unfold_attr);
                               unfold_tac = (uu___180_14683.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14683.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14683.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14683.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14683.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14683.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14683.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14685 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14685.tcenv);
                               debug = (uu___181_14685.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14685.primitive_steps);
                               strong = (uu___181_14685.strong);
                               memoize_lazy = (uu___181_14685.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14685.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14687 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14687 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14719  -> dummy :: env1) env)
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
                                          let uu____14760 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14760)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14765 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14765.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14765.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14766 -> lopt  in
                           (log cfg
                              (fun uu____14772  ->
                                 let uu____14773 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14773);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14782 = cfg  in
                               {
                                 steps = (uu___183_14782.steps);
                                 tcenv = (uu___183_14782.tcenv);
                                 debug = (uu___183_14782.debug);
                                 delta_level = (uu___183_14782.delta_level);
                                 primitive_steps =
                                   (uu___183_14782.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14782.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14782.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14785)::uu____14786 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14798 = cfg.steps  in
                             {
                               beta = (uu___180_14798.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14798.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14798.unfold_until);
                               unfold_only = (uu___180_14798.unfold_only);
                               unfold_fully = (uu___180_14798.unfold_fully);
                               unfold_attr = (uu___180_14798.unfold_attr);
                               unfold_tac = (uu___180_14798.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14798.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14798.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14798.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14798.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14798.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14798.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14800 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14800.tcenv);
                               debug = (uu___181_14800.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14800.primitive_steps);
                               strong = (uu___181_14800.strong);
                               memoize_lazy = (uu___181_14800.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14800.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14802 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14802 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14834  -> dummy :: env1) env)
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
                                          let uu____14875 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14875)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14880 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14880.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14880.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14881 -> lopt  in
                           (log cfg
                              (fun uu____14887  ->
                                 let uu____14888 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14888);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14897 = cfg  in
                               {
                                 steps = (uu___183_14897.steps);
                                 tcenv = (uu___183_14897.tcenv);
                                 debug = (uu___183_14897.debug);
                                 delta_level = (uu___183_14897.delta_level);
                                 primitive_steps =
                                   (uu___183_14897.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14897.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14897.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14900)::uu____14901 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14915 = cfg.steps  in
                             {
                               beta = (uu___180_14915.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14915.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14915.unfold_until);
                               unfold_only = (uu___180_14915.unfold_only);
                               unfold_fully = (uu___180_14915.unfold_fully);
                               unfold_attr = (uu___180_14915.unfold_attr);
                               unfold_tac = (uu___180_14915.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14915.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14915.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14915.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14915.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14915.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14915.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14917 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14917.tcenv);
                               debug = (uu___181_14917.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14917.primitive_steps);
                               strong = (uu___181_14917.strong);
                               memoize_lazy = (uu___181_14917.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14917.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14919 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14919 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14951  -> dummy :: env1) env)
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
                                          let uu____14992 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14992)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14997 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14997.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14997.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14998 -> lopt  in
                           (log cfg
                              (fun uu____15004  ->
                                 let uu____15005 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15005);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15014 = cfg  in
                               {
                                 steps = (uu___183_15014.steps);
                                 tcenv = (uu___183_15014.tcenv);
                                 debug = (uu___183_15014.debug);
                                 delta_level = (uu___183_15014.delta_level);
                                 primitive_steps =
                                   (uu___183_15014.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15014.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15014.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15017)::uu____15018 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_15032 = cfg.steps  in
                             {
                               beta = (uu___180_15032.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_15032.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_15032.unfold_until);
                               unfold_only = (uu___180_15032.unfold_only);
                               unfold_fully = (uu___180_15032.unfold_fully);
                               unfold_attr = (uu___180_15032.unfold_attr);
                               unfold_tac = (uu___180_15032.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_15032.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_15032.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_15032.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_15032.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_15032.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_15032.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_15034 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_15034.tcenv);
                               debug = (uu___181_15034.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_15034.primitive_steps);
                               strong = (uu___181_15034.strong);
                               memoize_lazy = (uu___181_15034.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_15034.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15036 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15036 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15068  -> dummy :: env1) env)
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
                                          let uu____15109 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15109)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15114 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15114.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15114.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15115 -> lopt  in
                           (log cfg
                              (fun uu____15121  ->
                                 let uu____15122 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15122);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15131 = cfg  in
                               {
                                 steps = (uu___183_15131.steps);
                                 tcenv = (uu___183_15131.tcenv);
                                 debug = (uu___183_15131.debug);
                                 delta_level = (uu___183_15131.delta_level);
                                 primitive_steps =
                                   (uu___183_15131.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15131.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15131.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15134)::uu____15135 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_15153 = cfg.steps  in
                             {
                               beta = (uu___180_15153.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_15153.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_15153.unfold_until);
                               unfold_only = (uu___180_15153.unfold_only);
                               unfold_fully = (uu___180_15153.unfold_fully);
                               unfold_attr = (uu___180_15153.unfold_attr);
                               unfold_tac = (uu___180_15153.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_15153.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_15153.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_15153.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_15153.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_15153.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_15153.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_15155 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_15155.tcenv);
                               debug = (uu___181_15155.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_15155.primitive_steps);
                               strong = (uu___181_15155.strong);
                               memoize_lazy = (uu___181_15155.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_15155.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15157 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15157 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15189  -> dummy :: env1) env)
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
                                          let uu____15230 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15230)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15235 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15235.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15235.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15236 -> lopt  in
                           (log cfg
                              (fun uu____15242  ->
                                 let uu____15243 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15243);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15252 = cfg  in
                               {
                                 steps = (uu___183_15252.steps);
                                 tcenv = (uu___183_15252.tcenv);
                                 debug = (uu___183_15252.debug);
                                 delta_level = (uu___183_15252.delta_level);
                                 primitive_steps =
                                   (uu___183_15252.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15252.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15252.normalize_pure_lets)
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
                             let uu___180_15258 = cfg.steps  in
                             {
                               beta = (uu___180_15258.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_15258.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_15258.unfold_until);
                               unfold_only = (uu___180_15258.unfold_only);
                               unfold_fully = (uu___180_15258.unfold_fully);
                               unfold_attr = (uu___180_15258.unfold_attr);
                               unfold_tac = (uu___180_15258.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_15258.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_15258.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_15258.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_15258.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_15258.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_15258.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_15260 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_15260.tcenv);
                               debug = (uu___181_15260.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_15260.primitive_steps);
                               strong = (uu___181_15260.strong);
                               memoize_lazy = (uu___181_15260.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_15260.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15262 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15262 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15294  -> dummy :: env1) env)
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
                                          let uu____15335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15340 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15340.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15340.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15341 -> lopt  in
                           (log cfg
                              (fun uu____15347  ->
                                 let uu____15348 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15348);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15357 = cfg  in
                               {
                                 steps = (uu___183_15357.steps);
                                 tcenv = (uu___183_15357.tcenv);
                                 debug = (uu___183_15357.debug);
                                 delta_level = (uu___183_15357.delta_level);
                                 primitive_steps =
                                   (uu___183_15357.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15357.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15357.normalize_pure_lets)
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
                      (fun uu____15396  ->
                         fun stack1  ->
                           match uu____15396 with
                           | (a,aq) ->
                               let uu____15408 =
                                 let uu____15409 =
                                   let uu____15416 =
                                     let uu____15417 =
                                       let uu____15448 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15448, false)  in
                                     Clos uu____15417  in
                                   (uu____15416, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15409  in
                               uu____15408 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15536  ->
                     let uu____15537 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15537);
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
                             ((let uu___184_15583 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_15583.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_15583.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15584 ->
                      let uu____15599 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15599)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15602 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15602 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15627 =
                          let uu____15628 =
                            let uu____15635 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___185_15641 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___185_15641.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___185_15641.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15635)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15628  in
                        mk uu____15627 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15660 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15660
               else
                 (let uu____15662 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15662 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15670 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15692  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15670 c1  in
                      let t2 =
                        let uu____15714 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15714 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15825)::uu____15826 ->
                    (log cfg
                       (fun uu____15839  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15840)::uu____15841 ->
                    (log cfg
                       (fun uu____15852  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15853,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15854;
                                   FStar_Syntax_Syntax.vars = uu____15855;_},uu____15856,uu____15857))::uu____15858
                    ->
                    (log cfg
                       (fun uu____15865  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15866)::uu____15867 ->
                    (log cfg
                       (fun uu____15878  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15879 ->
                    (log cfg
                       (fun uu____15882  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15886  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15911 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15911
                         | FStar_Util.Inr c ->
                             let uu____15921 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____15921
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____15940 =
                               let uu____15941 =
                                 let uu____15968 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____15968, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15941
                                in
                             mk uu____15940 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16003 ->
                           let uu____16004 =
                             let uu____16005 =
                               let uu____16006 =
                                 let uu____16033 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16033, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16006
                                in
                             mk uu____16005 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16004))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___186_16110 = cfg  in
                   {
                     steps =
                       (let uu___187_16113 = cfg.steps  in
                        {
                          beta = (uu___187_16113.beta);
                          iota = (uu___187_16113.iota);
                          zeta = (uu___187_16113.zeta);
                          weak = true;
                          hnf = (uu___187_16113.hnf);
                          primops = (uu___187_16113.primops);
                          do_not_unfold_pure_lets =
                            (uu___187_16113.do_not_unfold_pure_lets);
                          unfold_until = (uu___187_16113.unfold_until);
                          unfold_only = (uu___187_16113.unfold_only);
                          unfold_fully = (uu___187_16113.unfold_fully);
                          unfold_attr = (uu___187_16113.unfold_attr);
                          unfold_tac = (uu___187_16113.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___187_16113.pure_subterms_within_computations);
                          simplify = (uu___187_16113.simplify);
                          erase_universes = (uu___187_16113.erase_universes);
                          allow_unbound_universes =
                            (uu___187_16113.allow_unbound_universes);
                          reify_ = (uu___187_16113.reify_);
                          compress_uvars = (uu___187_16113.compress_uvars);
                          no_full_norm = (uu___187_16113.no_full_norm);
                          check_no_uvars = (uu___187_16113.check_no_uvars);
                          unmeta = (uu___187_16113.unmeta);
                          unascribe = (uu___187_16113.unascribe);
                          in_full_norm_request =
                            (uu___187_16113.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___187_16113.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___186_16110.tcenv);
                     debug = (uu___186_16110.debug);
                     delta_level = (uu___186_16110.delta_level);
                     primitive_steps = (uu___186_16110.primitive_steps);
                     strong = (uu___186_16110.strong);
                     memoize_lazy = (uu___186_16110.memoize_lazy);
                     normalize_pure_lets =
                       (uu___186_16110.normalize_pure_lets)
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
                         let uu____16149 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16149 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___188_16169 = cfg  in
                               let uu____16170 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___188_16169.steps);
                                 tcenv = uu____16170;
                                 debug = (uu___188_16169.debug);
                                 delta_level = (uu___188_16169.delta_level);
                                 primitive_steps =
                                   (uu___188_16169.primitive_steps);
                                 strong = (uu___188_16169.strong);
                                 memoize_lazy = (uu___188_16169.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_16169.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16177 =
                                 let uu____16178 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16178  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16177
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___189_16181 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___189_16181.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___189_16181.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___189_16181.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___189_16181.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16182 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16182
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16193,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16194;
                               FStar_Syntax_Syntax.lbunivs = uu____16195;
                               FStar_Syntax_Syntax.lbtyp = uu____16196;
                               FStar_Syntax_Syntax.lbeff = uu____16197;
                               FStar_Syntax_Syntax.lbdef = uu____16198;
                               FStar_Syntax_Syntax.lbattrs = uu____16199;
                               FStar_Syntax_Syntax.lbpos = uu____16200;_}::uu____16201),uu____16202)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16242 =
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
               if uu____16242
               then
                 let binder =
                   let uu____16244 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16244  in
                 let env1 =
                   let uu____16254 =
                     let uu____16261 =
                       let uu____16262 =
                         let uu____16293 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16293,
                           false)
                          in
                       Clos uu____16262  in
                     ((FStar_Pervasives_Native.Some binder), uu____16261)  in
                   uu____16254 :: env  in
                 (log cfg
                    (fun uu____16388  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16392  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16393 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16393))
                 else
                   (let uu____16395 =
                      let uu____16400 =
                        let uu____16401 =
                          let uu____16406 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16406
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16401]  in
                      FStar_Syntax_Subst.open_term uu____16400 body  in
                    match uu____16395 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16427  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16435 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16435  in
                            FStar_Util.Inl
                              (let uu___190_16445 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___190_16445.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___190_16445.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16448  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___191_16450 = lb  in
                             let uu____16451 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___191_16450.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___191_16450.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16451;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___191_16450.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___191_16450.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16476  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___192_16499 = cfg  in
                             {
                               steps = (uu___192_16499.steps);
                               tcenv = (uu___192_16499.tcenv);
                               debug = (uu___192_16499.debug);
                               delta_level = (uu___192_16499.delta_level);
                               primitive_steps =
                                 (uu___192_16499.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___192_16499.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___192_16499.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16502  ->
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
               let uu____16519 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16519 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16555 =
                               let uu___193_16556 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___193_16556.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___193_16556.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16555  in
                           let uu____16557 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16557 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16583 =
                                   FStar_List.map (fun uu____16599  -> dummy)
                                     lbs1
                                    in
                                 let uu____16600 =
                                   let uu____16609 =
                                     FStar_List.map
                                       (fun uu____16629  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16609 env  in
                                 FStar_List.append uu____16583 uu____16600
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16653 =
                                       let uu___194_16654 = rc  in
                                       let uu____16655 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___194_16654.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16655;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___194_16654.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16653
                                 | uu____16664 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___195_16670 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___195_16670.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___195_16670.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___195_16670.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___195_16670.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16680 =
                        FStar_List.map (fun uu____16696  -> dummy) lbs2  in
                      FStar_List.append uu____16680 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16704 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16704 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___196_16720 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___196_16720.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___196_16720.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16749 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16749
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16768 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16844  ->
                        match uu____16844 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___197_16965 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___197_16965.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___197_16965.FStar_Syntax_Syntax.sort)
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
               (match uu____16768 with
                | (rec_env,memos,uu____17192) ->
                    let uu____17245 =
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
                             let uu____17568 =
                               let uu____17575 =
                                 let uu____17576 =
                                   let uu____17607 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17607, false)
                                    in
                                 Clos uu____17576  in
                               (FStar_Pervasives_Native.None, uu____17575)
                                in
                             uu____17568 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17711  ->
                     let uu____17712 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17712);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____17734 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17736::uu____17737 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17742) ->
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
                             | uu____17765 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17779 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17779
                              | uu____17790 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17796 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17822 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17838 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17853 =
                        let uu____17854 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17855 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17854 uu____17855
                         in
                      failwith uu____17853
                    else
                      (let uu____17857 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____17857)
                | uu____17858 -> norm cfg env stack t2))

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
                let uu____17868 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____17868  in
              let uu____17869 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17869 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____17882  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____17893  ->
                        let uu____17894 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17895 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____17894 uu____17895);
                   (let t1 =
                      if
                        (cfg.steps).unfold_until =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        (let uu____17900 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____17900 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____17909))::stack1 ->
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
                      | uu____17948 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____17951 ->
                          let uu____17954 =
                            let uu____17955 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17955
                             in
                          failwith uu____17954
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
                  let uu___198_17979 = cfg  in
                  let uu____17980 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____17980;
                    tcenv = (uu___198_17979.tcenv);
                    debug = (uu___198_17979.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___198_17979.primitive_steps);
                    strong = (uu___198_17979.strong);
                    memoize_lazy = (uu___198_17979.memoize_lazy);
                    normalize_pure_lets =
                      (uu___198_17979.normalize_pure_lets)
                  }
                else
                  (let uu___199_17982 = cfg  in
                   {
                     steps =
                       (let uu___200_17985 = cfg.steps  in
                        {
                          beta = (uu___200_17985.beta);
                          iota = (uu___200_17985.iota);
                          zeta = false;
                          weak = (uu___200_17985.weak);
                          hnf = (uu___200_17985.hnf);
                          primops = (uu___200_17985.primops);
                          do_not_unfold_pure_lets =
                            (uu___200_17985.do_not_unfold_pure_lets);
                          unfold_until = (uu___200_17985.unfold_until);
                          unfold_only = (uu___200_17985.unfold_only);
                          unfold_fully = (uu___200_17985.unfold_fully);
                          unfold_attr = (uu___200_17985.unfold_attr);
                          unfold_tac = (uu___200_17985.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___200_17985.pure_subterms_within_computations);
                          simplify = (uu___200_17985.simplify);
                          erase_universes = (uu___200_17985.erase_universes);
                          allow_unbound_universes =
                            (uu___200_17985.allow_unbound_universes);
                          reify_ = (uu___200_17985.reify_);
                          compress_uvars = (uu___200_17985.compress_uvars);
                          no_full_norm = (uu___200_17985.no_full_norm);
                          check_no_uvars = (uu___200_17985.check_no_uvars);
                          unmeta = (uu___200_17985.unmeta);
                          unascribe = (uu___200_17985.unascribe);
                          in_full_norm_request =
                            (uu___200_17985.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___200_17985.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___199_17982.tcenv);
                     debug = (uu___199_17982.debug);
                     delta_level = (uu___199_17982.delta_level);
                     primitive_steps = (uu___199_17982.primitive_steps);
                     strong = (uu___199_17982.strong);
                     memoize_lazy = (uu___199_17982.memoize_lazy);
                     normalize_pure_lets =
                       (uu___199_17982.normalize_pure_lets)
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
                  (fun uu____18019  ->
                     let uu____18020 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18021 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18020
                       uu____18021);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18023 =
                   let uu____18024 = FStar_Syntax_Subst.compress head3  in
                   uu____18024.FStar_Syntax_Syntax.n  in
                 match uu____18023 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18042 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18042
                        in
                     let uu____18043 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18043 with
                      | (uu____18044,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18054 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18064 =
                                   let uu____18065 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18065.FStar_Syntax_Syntax.n  in
                                 match uu____18064 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18071,uu____18072))
                                     ->
                                     let uu____18081 =
                                       let uu____18082 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18082.FStar_Syntax_Syntax.n  in
                                     (match uu____18081 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18088,msrc,uu____18090))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18099 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18099
                                      | uu____18100 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18101 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18102 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18102 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___201_18107 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___201_18107.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___201_18107.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___201_18107.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___201_18107.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___201_18107.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18108 = FStar_List.tl stack  in
                                    let uu____18109 =
                                      let uu____18110 =
                                        let uu____18117 =
                                          let uu____18118 =
                                            let uu____18131 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18131)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18118
                                           in
                                        FStar_Syntax_Syntax.mk uu____18117
                                         in
                                      uu____18110
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18108 uu____18109
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18147 =
                                      let uu____18148 = is_return body  in
                                      match uu____18148 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18152;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18153;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18156 -> false  in
                                    if uu____18147
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
                                         let uu____18177 =
                                           let uu____18184 =
                                             let uu____18185 =
                                               let uu____18202 =
                                                 let uu____18209 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18209]  in
                                               (uu____18202, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18185
                                              in
                                           FStar_Syntax_Syntax.mk uu____18184
                                            in
                                         uu____18177
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18243 =
                                           let uu____18244 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18244.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18243 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18250::uu____18251::[])
                                             ->
                                             let uu____18256 =
                                               let uu____18263 =
                                                 let uu____18264 =
                                                   let uu____18271 =
                                                     let uu____18272 =
                                                       let uu____18273 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18273
                                                        in
                                                     let uu____18274 =
                                                       let uu____18277 =
                                                         let uu____18278 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18278
                                                          in
                                                       [uu____18277]  in
                                                     uu____18272 ::
                                                       uu____18274
                                                      in
                                                   (bind1, uu____18271)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18264
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18263
                                                in
                                             uu____18256
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18284 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18296 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18296
                                         then
                                           let uu____18305 =
                                             let uu____18312 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18312
                                              in
                                           let uu____18313 =
                                             let uu____18322 =
                                               let uu____18329 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18329
                                                in
                                             [uu____18322]  in
                                           uu____18305 :: uu____18313
                                         else []  in
                                       let reified =
                                         let uu____18358 =
                                           let uu____18365 =
                                             let uu____18366 =
                                               let uu____18381 =
                                                 let uu____18390 =
                                                   let uu____18399 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18406 =
                                                     let uu____18415 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18415]  in
                                                   uu____18399 :: uu____18406
                                                    in
                                                 let uu____18440 =
                                                   let uu____18449 =
                                                     let uu____18458 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18465 =
                                                       let uu____18474 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18481 =
                                                         let uu____18490 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18497 =
                                                           let uu____18506 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18506]  in
                                                         uu____18490 ::
                                                           uu____18497
                                                          in
                                                       uu____18474 ::
                                                         uu____18481
                                                        in
                                                     uu____18458 ::
                                                       uu____18465
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18449
                                                    in
                                                 FStar_List.append
                                                   uu____18390 uu____18440
                                                  in
                                               (bind_inst, uu____18381)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18366
                                              in
                                           FStar_Syntax_Syntax.mk uu____18365
                                            in
                                         uu____18358
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18572  ->
                                            let uu____18573 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18574 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18573 uu____18574);
                                       (let uu____18575 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18575 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18599 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18599
                        in
                     let uu____18600 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18600 with
                      | (uu____18601,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18638 =
                                  let uu____18639 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18639.FStar_Syntax_Syntax.n  in
                                match uu____18638 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18643) -> t2
                                | uu____18648 -> head4  in
                              let uu____18649 =
                                let uu____18650 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18650.FStar_Syntax_Syntax.n  in
                              match uu____18649 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18656 -> FStar_Pervasives_Native.None
                               in
                            let uu____18657 = maybe_extract_fv head4  in
                            match uu____18657 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18667 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18667
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18672 = maybe_extract_fv head5
                                     in
                                  match uu____18672 with
                                  | FStar_Pervasives_Native.Some uu____18677
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18678 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18683 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18698 =
                              match uu____18698 with
                              | (e,q) ->
                                  let uu____18705 =
                                    let uu____18706 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18706.FStar_Syntax_Syntax.n  in
                                  (match uu____18705 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____18721 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____18721
                                   | uu____18722 -> false)
                               in
                            let uu____18723 =
                              let uu____18724 =
                                let uu____18733 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18733 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18724
                               in
                            if uu____18723
                            then
                              let uu____18752 =
                                let uu____18753 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18753
                                 in
                              failwith uu____18752
                            else ());
                           (let uu____18755 = maybe_unfold_action head_app
                               in
                            match uu____18755 with
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
                                   (fun uu____18798  ->
                                      let uu____18799 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18800 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18799 uu____18800);
                                 (let uu____18801 = FStar_List.tl stack  in
                                  norm cfg env uu____18801 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18803) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18827 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18827  in
                     (log cfg
                        (fun uu____18831  ->
                           let uu____18832 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18832);
                      (let uu____18833 = FStar_List.tl stack  in
                       norm cfg env uu____18833 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18954  ->
                               match uu____18954 with
                               | (pat,wopt,tm) ->
                                   let uu____19002 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19002)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19034 = FStar_List.tl stack  in
                     norm cfg env uu____19034 tm
                 | uu____19035 -> fallback ())

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
              (fun uu____19049  ->
                 let uu____19050 = FStar_Ident.string_of_lid msrc  in
                 let uu____19051 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19052 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19050
                   uu____19051 uu____19052);
            (let uu____19053 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19053
             then
               let ed =
                 let uu____19055 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19055  in
               let uu____19056 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19056 with
               | (uu____19057,return_repr) ->
                   let return_inst =
                     let uu____19070 =
                       let uu____19071 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19071.FStar_Syntax_Syntax.n  in
                     match uu____19070 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19077::[]) ->
                         let uu____19082 =
                           let uu____19089 =
                             let uu____19090 =
                               let uu____19097 =
                                 let uu____19098 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19098]  in
                               (return_tm, uu____19097)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19090  in
                           FStar_Syntax_Syntax.mk uu____19089  in
                         uu____19082 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19104 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19107 =
                     let uu____19114 =
                       let uu____19115 =
                         let uu____19130 =
                           let uu____19139 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19146 =
                             let uu____19155 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19155]  in
                           uu____19139 :: uu____19146  in
                         (return_inst, uu____19130)  in
                       FStar_Syntax_Syntax.Tm_app uu____19115  in
                     FStar_Syntax_Syntax.mk uu____19114  in
                   uu____19107 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19194 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19194 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19197 =
                      let uu____19198 = FStar_Ident.text_of_lid msrc  in
                      let uu____19199 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19198 uu____19199
                       in
                    failwith uu____19197
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19200;
                      FStar_TypeChecker_Env.mtarget = uu____19201;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19202;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19224 =
                      let uu____19225 = FStar_Ident.text_of_lid msrc  in
                      let uu____19226 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19225 uu____19226
                       in
                    failwith uu____19224
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19227;
                      FStar_TypeChecker_Env.mtarget = uu____19228;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19229;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____19264 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____19265 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____19264 t FStar_Syntax_Syntax.tun uu____19265))

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
                (fun uu____19321  ->
                   match uu____19321 with
                   | (a,imp) ->
                       let uu____19332 = norm cfg env [] a  in
                       (uu____19332, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____19340  ->
             let uu____19341 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____19342 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____19341 uu____19342);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19366 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____19366
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___202_19369 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___202_19369.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___202_19369.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19391 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____19391
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___203_19394 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___203_19394.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___203_19394.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____19431  ->
                      match uu____19431 with
                      | (a,i) ->
                          let uu____19442 = norm cfg env [] a  in
                          (uu____19442, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___116_19460  ->
                       match uu___116_19460 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____19464 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____19464
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___204_19472 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___205_19475 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___205_19475.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___204_19472.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___204_19472.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19478  ->
        match uu____19478 with
        | (x,imp) ->
            let uu____19481 =
              let uu___206_19482 = x  in
              let uu____19483 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___206_19482.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___206_19482.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19483
              }  in
            (uu____19481, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19489 =
          FStar_List.fold_left
            (fun uu____19523  ->
               fun b  ->
                 match uu____19523 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19489 with | (nbs,uu____19603) -> FStar_List.rev nbs

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
            let uu____19635 =
              let uu___207_19636 = rc  in
              let uu____19637 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___207_19636.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19637;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___207_19636.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19635
        | uu____19646 -> lopt

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
            (let uu____19667 = FStar_Syntax_Print.term_to_string tm  in
             let uu____19668 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____19667
               uu____19668)
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
          let uu____19690 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____19690
          then tm1
          else
            (let w t =
               let uu___208_19704 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___208_19704.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___208_19704.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____19715 =
                 let uu____19716 = FStar_Syntax_Util.unmeta t  in
                 uu____19716.FStar_Syntax_Syntax.n  in
               match uu____19715 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____19723 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____19772)::args1,(bv,uu____19775)::bs1) ->
                   let uu____19809 =
                     let uu____19810 = FStar_Syntax_Subst.compress t  in
                     uu____19810.FStar_Syntax_Syntax.n  in
                   (match uu____19809 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____19814 -> false)
               | ([],[]) -> true
               | (uu____19835,uu____19836) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19877 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19878 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____19877
                    uu____19878)
               else ();
               (let uu____19880 = FStar_Syntax_Util.head_and_args' t  in
                match uu____19880 with
                | (hd1,args) ->
                    let uu____19913 =
                      let uu____19914 = FStar_Syntax_Subst.compress hd1  in
                      uu____19914.FStar_Syntax_Syntax.n  in
                    (match uu____19913 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____19921 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____19922 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____19923 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____19921 uu____19922 uu____19923)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____19925 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19942 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19943 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____19942
                    uu____19943)
               else ();
               (let uu____19945 = FStar_Syntax_Util.is_squash t  in
                match uu____19945 with
                | FStar_Pervasives_Native.Some (uu____19956,t') ->
                    is_applied bs t'
                | uu____19968 ->
                    let uu____19977 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____19977 with
                     | FStar_Pervasives_Native.Some (uu____19988,t') ->
                         is_applied bs t'
                     | uu____20000 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20024 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20024 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20031)::(q,uu____20033)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20061 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20062 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20061 uu____20062)
                    else ();
                    (let uu____20064 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20064 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20069 =
                           let uu____20070 = FStar_Syntax_Subst.compress p
                              in
                           uu____20070.FStar_Syntax_Syntax.n  in
                         (match uu____20069 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20078 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20078))
                          | uu____20081 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20084)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20101 =
                           let uu____20102 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20102.FStar_Syntax_Syntax.n  in
                         (match uu____20101 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20110 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20110))
                          | uu____20113 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20117 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20117 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20122 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20122 with
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
                                     let uu____20133 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20133))
                               | uu____20136 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____20141)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____20158 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____20158 with
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
                                     let uu____20169 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20169))
                               | uu____20172 -> FStar_Pervasives_Native.None)
                          | uu____20175 -> FStar_Pervasives_Native.None)
                     | uu____20178 -> FStar_Pervasives_Native.None))
               | uu____20181 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____20194 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20194 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____20200)::[],uu____20201,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20212 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____20213 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____20212
                         uu____20213)
                    else ();
                    is_quantified_const bv phi')
               | uu____20215 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____20228 =
                 let uu____20229 = FStar_Syntax_Subst.compress phi  in
                 uu____20229.FStar_Syntax_Syntax.n  in
               match uu____20228 with
               | FStar_Syntax_Syntax.Tm_match (uu____20234,br::brs) ->
                   let uu____20301 = br  in
                   (match uu____20301 with
                    | (uu____20318,uu____20319,e) ->
                        let r =
                          let uu____20340 = simp_t e  in
                          match uu____20340 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____20346 =
                                FStar_List.for_all
                                  (fun uu____20364  ->
                                     match uu____20364 with
                                     | (uu____20377,uu____20378,e') ->
                                         let uu____20392 = simp_t e'  in
                                         uu____20392 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____20346
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____20400 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____20409 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____20409
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____20440 =
                 match uu____20440 with
                 | (t1,q) ->
                     let uu____20453 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____20453 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____20481 -> (t1, q))
                  in
               let uu____20492 = FStar_Syntax_Util.head_and_args t  in
               match uu____20492 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____20558 =
                 let uu____20559 = FStar_Syntax_Util.unmeta ty  in
                 uu____20559.FStar_Syntax_Syntax.n  in
               match uu____20558 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____20563) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____20568,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____20588 -> false  in
             let simplify1 arg =
               let uu____20613 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____20613, arg)  in
             let uu____20622 = is_forall_const tm1  in
             match uu____20622 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____20627 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____20628 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____20627
                       uu____20628)
                  else ();
                  (let uu____20630 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____20630))
             | FStar_Pervasives_Native.None  ->
                 let uu____20631 =
                   let uu____20632 = FStar_Syntax_Subst.compress tm1  in
                   uu____20632.FStar_Syntax_Syntax.n  in
                 (match uu____20631 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____20636;
                              FStar_Syntax_Syntax.vars = uu____20637;_},uu____20638);
                         FStar_Syntax_Syntax.pos = uu____20639;
                         FStar_Syntax_Syntax.vars = uu____20640;_},args)
                      ->
                      let uu____20666 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20666
                      then
                        let uu____20667 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20667 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20712)::
                             (uu____20713,(arg,uu____20715))::[] ->
                             maybe_auto_squash arg
                         | (uu____20764,(arg,uu____20766))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20767)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20816)::uu____20817::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20868::(FStar_Pervasives_Native.Some (false
                                         ),uu____20869)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20920 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20934 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20934
                         then
                           let uu____20935 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20935 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20980)::uu____20981::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21032::(FStar_Pervasives_Native.Some (true
                                           ),uu____21033)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21084)::(uu____21085,(arg,uu____21087))::[]
                               -> maybe_auto_squash arg
                           | (uu____21136,(arg,uu____21138))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21139)::[]
                               -> maybe_auto_squash arg
                           | uu____21188 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21202 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21202
                            then
                              let uu____21203 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21203 with
                              | uu____21248::(FStar_Pervasives_Native.Some
                                              (true ),uu____21249)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21300)::uu____21301::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21352)::(uu____21353,(arg,uu____21355))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21404,(p,uu____21406))::(uu____21407,
                                                                (q,uu____21409))::[]
                                  ->
                                  let uu____21456 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21456
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21458 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21472 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21472
                               then
                                 let uu____21473 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21473 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21518)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21519)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21570)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21571)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21622)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21623)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21674)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21675)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21726,(arg,uu____21728))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21729)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21778)::(uu____21779,(arg,uu____21781))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21830,(arg,uu____21832))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21833)::[]
                                     ->
                                     let uu____21882 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21882
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21883)::(uu____21884,(arg,uu____21886))::[]
                                     ->
                                     let uu____21935 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21935
                                 | (uu____21936,(p,uu____21938))::(uu____21939,
                                                                   (q,uu____21941))::[]
                                     ->
                                     let uu____21988 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21988
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21990 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22004 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22004
                                  then
                                    let uu____22005 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22005 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22050)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22081)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22112 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22126 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22126
                                     then
                                       match args with
                                       | (t,uu____22128)::[] ->
                                           let uu____22145 =
                                             let uu____22146 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22146.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22145 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22149::[],body,uu____22151)
                                                ->
                                                let uu____22178 = simp_t body
                                                   in
                                                (match uu____22178 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22181 -> tm1)
                                            | uu____22184 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22186))::(t,uu____22188)::[]
                                           ->
                                           let uu____22215 =
                                             let uu____22216 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22216.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22215 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22219::[],body,uu____22221)
                                                ->
                                                let uu____22248 = simp_t body
                                                   in
                                                (match uu____22248 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22251 -> tm1)
                                            | uu____22254 -> tm1)
                                       | uu____22255 -> tm1
                                     else
                                       (let uu____22265 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22265
                                        then
                                          match args with
                                          | (t,uu____22267)::[] ->
                                              let uu____22284 =
                                                let uu____22285 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22285.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22284 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22288::[],body,uu____22290)
                                                   ->
                                                   let uu____22317 =
                                                     simp_t body  in
                                                   (match uu____22317 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22320 -> tm1)
                                               | uu____22323 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22325))::(t,uu____22327)::[]
                                              ->
                                              let uu____22354 =
                                                let uu____22355 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22355.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22354 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22358::[],body,uu____22360)
                                                   ->
                                                   let uu____22387 =
                                                     simp_t body  in
                                                   (match uu____22387 with
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
                                                    | uu____22390 -> tm1)
                                               | uu____22393 -> tm1)
                                          | uu____22394 -> tm1
                                        else
                                          (let uu____22404 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22404
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22405;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22406;_},uu____22407)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22424;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22425;_},uu____22426)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22443 -> tm1
                                           else
                                             (let uu____22453 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22453 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22473 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22483;
                         FStar_Syntax_Syntax.vars = uu____22484;_},args)
                      ->
                      let uu____22506 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22506
                      then
                        let uu____22507 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22507 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22552)::
                             (uu____22553,(arg,uu____22555))::[] ->
                             maybe_auto_squash arg
                         | (uu____22604,(arg,uu____22606))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22607)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22656)::uu____22657::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22708::(FStar_Pervasives_Native.Some (false
                                         ),uu____22709)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22760 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22774 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22774
                         then
                           let uu____22775 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22775 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22820)::uu____22821::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22872::(FStar_Pervasives_Native.Some (true
                                           ),uu____22873)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22924)::(uu____22925,(arg,uu____22927))::[]
                               -> maybe_auto_squash arg
                           | (uu____22976,(arg,uu____22978))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22979)::[]
                               -> maybe_auto_squash arg
                           | uu____23028 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23042 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23042
                            then
                              let uu____23043 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23043 with
                              | uu____23088::(FStar_Pervasives_Native.Some
                                              (true ),uu____23089)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23140)::uu____23141::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23192)::(uu____23193,(arg,uu____23195))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23244,(p,uu____23246))::(uu____23247,
                                                                (q,uu____23249))::[]
                                  ->
                                  let uu____23296 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23296
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23298 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23312 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23312
                               then
                                 let uu____23313 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23313 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23358)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23359)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23410)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23411)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23462)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23463)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23514)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23515)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23566,(arg,uu____23568))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23569)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23618)::(uu____23619,(arg,uu____23621))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23670,(arg,uu____23672))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23673)::[]
                                     ->
                                     let uu____23722 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23722
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23723)::(uu____23724,(arg,uu____23726))::[]
                                     ->
                                     let uu____23775 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23775
                                 | (uu____23776,(p,uu____23778))::(uu____23779,
                                                                   (q,uu____23781))::[]
                                     ->
                                     let uu____23828 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23828
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23830 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23844 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23844
                                  then
                                    let uu____23845 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23845 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23890)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23921)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23952 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23966 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23966
                                     then
                                       match args with
                                       | (t,uu____23968)::[] ->
                                           let uu____23985 =
                                             let uu____23986 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23986.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23985 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23989::[],body,uu____23991)
                                                ->
                                                let uu____24018 = simp_t body
                                                   in
                                                (match uu____24018 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24021 -> tm1)
                                            | uu____24024 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24026))::(t,uu____24028)::[]
                                           ->
                                           let uu____24055 =
                                             let uu____24056 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24056.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24055 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24059::[],body,uu____24061)
                                                ->
                                                let uu____24088 = simp_t body
                                                   in
                                                (match uu____24088 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24091 -> tm1)
                                            | uu____24094 -> tm1)
                                       | uu____24095 -> tm1
                                     else
                                       (let uu____24105 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24105
                                        then
                                          match args with
                                          | (t,uu____24107)::[] ->
                                              let uu____24124 =
                                                let uu____24125 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24125.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24124 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24128::[],body,uu____24130)
                                                   ->
                                                   let uu____24157 =
                                                     simp_t body  in
                                                   (match uu____24157 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24160 -> tm1)
                                               | uu____24163 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24165))::(t,uu____24167)::[]
                                              ->
                                              let uu____24194 =
                                                let uu____24195 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24195.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24194 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24198::[],body,uu____24200)
                                                   ->
                                                   let uu____24227 =
                                                     simp_t body  in
                                                   (match uu____24227 with
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
                                                    | uu____24230 -> tm1)
                                               | uu____24233 -> tm1)
                                          | uu____24234 -> tm1
                                        else
                                          (let uu____24244 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24244
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24245;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24246;_},uu____24247)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24264;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24265;_},uu____24266)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24283 -> tm1
                                           else
                                             (let uu____24293 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24293 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24313 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24328 = simp_t t  in
                      (match uu____24328 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24331 ->
                      let uu____24354 = is_const_match tm1  in
                      (match uu____24354 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24357 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____24367  ->
               (let uu____24369 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24370 = FStar_Syntax_Print.term_to_string t  in
                let uu____24371 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24378 =
                  let uu____24379 =
                    let uu____24382 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24382
                     in
                  stack_to_string uu____24379  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24369 uu____24370 uu____24371 uu____24378);
               (let uu____24405 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24405
                then
                  let uu____24406 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24406 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24413 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24414 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24415 =
                          let uu____24416 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24416
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24413
                          uu____24414 uu____24415);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____24434 =
                     let uu____24435 =
                       let uu____24436 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____24436  in
                     FStar_Util.string_of_int uu____24435  in
                   let uu____24441 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____24442 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____24434 uu____24441 uu____24442)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____24448,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____24499  ->
                     let uu____24500 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____24500);
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
               let uu____24538 =
                 let uu___209_24539 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___209_24539.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___209_24539.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____24538
           | (Arg (Univ uu____24542,uu____24543,uu____24544))::uu____24545 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____24548,uu____24549))::uu____24550 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____24565,uu____24566),aq,r))::stack1
               when
               let uu____24616 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24616 ->
               let t2 =
                 let uu____24620 =
                   let uu____24625 =
                     let uu____24626 = closure_as_term cfg env_arg tm  in
                     (uu____24626, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____24625  in
                 uu____24620 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____24636),aq,r))::stack1 ->
               (log cfg
                  (fun uu____24689  ->
                     let uu____24690 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____24690);
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
                  (let uu____24702 = FStar_ST.op_Bang m  in
                   match uu____24702 with
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
                   | FStar_Pervasives_Native.Some (uu____24845,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____24898 =
                 log cfg
                   (fun uu____24902  ->
                      let uu____24903 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____24903);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____24909 =
                 let uu____24910 = FStar_Syntax_Subst.compress t1  in
                 uu____24910.FStar_Syntax_Syntax.n  in
               (match uu____24909 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____24937 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____24937  in
                    (log cfg
                       (fun uu____24941  ->
                          let uu____24942 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____24942);
                     (let uu____24943 = FStar_List.tl stack  in
                      norm cfg env1 uu____24943 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____24944);
                       FStar_Syntax_Syntax.pos = uu____24945;
                       FStar_Syntax_Syntax.vars = uu____24946;_},(e,uu____24948)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____24977 when
                    (cfg.steps).primops ->
                    let uu____24992 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____24992 with
                     | (hd1,args) ->
                         let uu____25029 =
                           let uu____25030 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____25030.FStar_Syntax_Syntax.n  in
                         (match uu____25029 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____25034 = find_prim_step cfg fv  in
                              (match uu____25034 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____25037; arity = uu____25038;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____25040;
                                     requires_binder_substitution =
                                       uu____25041;
                                     interpretation = uu____25042;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____25058 -> fallback " (3)" ())
                          | uu____25061 -> fallback " (4)" ()))
                | uu____25062 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____25085  ->
                     let uu____25086 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____25086);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____25095 =
                   log cfg1
                     (fun uu____25100  ->
                        let uu____25101 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____25102 =
                          let uu____25103 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____25130  ->
                                    match uu____25130 with
                                    | (p,uu____25140,uu____25141) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____25103
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____25101 uu____25102);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___117_25158  ->
                                match uu___117_25158 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____25159 -> false))
                         in
                      let steps =
                        let uu___210_25161 = cfg1.steps  in
                        {
                          beta = (uu___210_25161.beta);
                          iota = (uu___210_25161.iota);
                          zeta = false;
                          weak = (uu___210_25161.weak);
                          hnf = (uu___210_25161.hnf);
                          primops = (uu___210_25161.primops);
                          do_not_unfold_pure_lets =
                            (uu___210_25161.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___210_25161.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___210_25161.pure_subterms_within_computations);
                          simplify = (uu___210_25161.simplify);
                          erase_universes = (uu___210_25161.erase_universes);
                          allow_unbound_universes =
                            (uu___210_25161.allow_unbound_universes);
                          reify_ = (uu___210_25161.reify_);
                          compress_uvars = (uu___210_25161.compress_uvars);
                          no_full_norm = (uu___210_25161.no_full_norm);
                          check_no_uvars = (uu___210_25161.check_no_uvars);
                          unmeta = (uu___210_25161.unmeta);
                          unascribe = (uu___210_25161.unascribe);
                          in_full_norm_request =
                            (uu___210_25161.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___210_25161.weakly_reduce_scrutinee)
                        }  in
                      let uu___211_25166 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___211_25166.tcenv);
                        debug = (uu___211_25166.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___211_25166.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___211_25166.memoize_lazy);
                        normalize_pure_lets =
                          (uu___211_25166.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____25238 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____25267 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____25351  ->
                                    fun uu____25352  ->
                                      match (uu____25351, uu____25352) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____25491 = norm_pat env3 p1
                                             in
                                          (match uu____25491 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____25267 with
                           | (pats1,env3) ->
                               ((let uu___212_25653 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___212_25653.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___213_25672 = x  in
                            let uu____25673 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___213_25672.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___213_25672.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25673
                            }  in
                          ((let uu___214_25687 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___214_25687.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___215_25698 = x  in
                            let uu____25699 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___215_25698.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___215_25698.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25699
                            }  in
                          ((let uu___216_25713 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___216_25713.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___217_25729 = x  in
                            let uu____25730 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___217_25729.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___217_25729.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25730
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___218_25745 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___218_25745.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____25789 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____25805 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____25805 with
                                  | (p,wopt,e) ->
                                      let uu____25825 = norm_pat env1 p  in
                                      (match uu____25825 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____25880 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____25880
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____25893 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____25893
                      then
                        norm
                          (let uu___219_25898 = cfg1  in
                           {
                             steps =
                               (let uu___220_25901 = cfg1.steps  in
                                {
                                  beta = (uu___220_25901.beta);
                                  iota = (uu___220_25901.iota);
                                  zeta = (uu___220_25901.zeta);
                                  weak = (uu___220_25901.weak);
                                  hnf = (uu___220_25901.hnf);
                                  primops = (uu___220_25901.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___220_25901.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___220_25901.unfold_until);
                                  unfold_only = (uu___220_25901.unfold_only);
                                  unfold_fully =
                                    (uu___220_25901.unfold_fully);
                                  unfold_attr = (uu___220_25901.unfold_attr);
                                  unfold_tac = (uu___220_25901.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___220_25901.pure_subterms_within_computations);
                                  simplify = (uu___220_25901.simplify);
                                  erase_universes =
                                    (uu___220_25901.erase_universes);
                                  allow_unbound_universes =
                                    (uu___220_25901.allow_unbound_universes);
                                  reify_ = (uu___220_25901.reify_);
                                  compress_uvars =
                                    (uu___220_25901.compress_uvars);
                                  no_full_norm =
                                    (uu___220_25901.no_full_norm);
                                  check_no_uvars =
                                    (uu___220_25901.check_no_uvars);
                                  unmeta = (uu___220_25901.unmeta);
                                  unascribe = (uu___220_25901.unascribe);
                                  in_full_norm_request =
                                    (uu___220_25901.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___219_25898.tcenv);
                             debug = (uu___219_25898.debug);
                             delta_level = (uu___219_25898.delta_level);
                             primitive_steps =
                               (uu___219_25898.primitive_steps);
                             strong = (uu___219_25898.strong);
                             memoize_lazy = (uu___219_25898.memoize_lazy);
                             normalize_pure_lets =
                               (uu___219_25898.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____25903 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____25903)
                    in
                 let rec is_cons head1 =
                   let uu____25928 =
                     let uu____25929 = FStar_Syntax_Subst.compress head1  in
                     uu____25929.FStar_Syntax_Syntax.n  in
                   match uu____25928 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____25933) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____25938 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25939;
                         FStar_Syntax_Syntax.fv_delta = uu____25940;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25941;
                         FStar_Syntax_Syntax.fv_delta = uu____25942;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____25943);_}
                       -> true
                   | uu____25950 -> false  in
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
                   let uu____26113 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____26113 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____26200 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____26239 ->
                                 let uu____26240 =
                                   let uu____26241 = is_cons head1  in
                                   Prims.op_Negation uu____26241  in
                                 FStar_Util.Inr uu____26240)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____26266 =
                              let uu____26267 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____26267.FStar_Syntax_Syntax.n  in
                            (match uu____26266 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____26285 ->
                                 let uu____26286 =
                                   let uu____26287 = is_cons head1  in
                                   Prims.op_Negation uu____26287  in
                                 FStar_Util.Inr uu____26286))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____26364)::rest_a,(p1,uu____26367)::rest_p) ->
                       let uu____26411 = matches_pat t2 p1  in
                       (match uu____26411 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____26460 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____26578 = matches_pat scrutinee1 p1  in
                       (match uu____26578 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____26618  ->
                                  let uu____26619 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____26620 =
                                    let uu____26621 =
                                      FStar_List.map
                                        (fun uu____26631  ->
                                           match uu____26631 with
                                           | (uu____26636,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____26621
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____26619 uu____26620);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____26668  ->
                                       match uu____26668 with
                                       | (bv,t2) ->
                                           let uu____26691 =
                                             let uu____26698 =
                                               let uu____26701 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____26701
                                                in
                                             let uu____26702 =
                                               let uu____26703 =
                                                 let uu____26734 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____26734, false)
                                                  in
                                               Clos uu____26703  in
                                             (uu____26698, uu____26702)  in
                                           uu____26691 :: env2) env1 s
                                 in
                              let uu____26847 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____26847)))
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
    let uu____26874 =
      let uu____26877 = FStar_ST.op_Bang plugins  in p :: uu____26877  in
    FStar_ST.op_Colon_Equals plugins uu____26874  in
  let retrieve uu____26985 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____27062  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___118_27103  ->
                  match uu___118_27103 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____27107 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____27113 -> d  in
        let uu____27116 = to_fsteps s  in
        let uu____27117 =
          let uu____27118 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____27119 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____27120 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____27121 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____27122 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____27123 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____27124 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____27118;
            primop = uu____27119;
            unfolding = uu____27120;
            b380 = uu____27121;
            wpe = uu____27122;
            norm_delayed = uu____27123;
            print_normalized = uu____27124
          }  in
        let uu____27125 =
          let uu____27128 =
            let uu____27131 = retrieve_plugins ()  in
            FStar_List.append uu____27131 psteps  in
          add_steps built_in_primitive_steps uu____27128  in
        let uu____27134 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____27136 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____27136)
           in
        {
          steps = uu____27116;
          tcenv = e;
          debug = uu____27117;
          delta_level = d1;
          primitive_steps = uu____27125;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____27134
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
      fun t  -> let uu____27218 = config s e  in norm_comp uu____27218 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27235 = config [] env  in norm_universe uu____27235 [] u
  
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
        let uu____27259 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27259  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27266 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___221_27285 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___221_27285.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___221_27285.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27292 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27292
          then
            let ct1 =
              let uu____27294 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27294 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____27301 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27301
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___222_27305 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___222_27305.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___222_27305.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___222_27305.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___223_27307 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___223_27307.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___223_27307.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___223_27307.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___223_27307.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___224_27308 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___224_27308.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___224_27308.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27310 -> c
  
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
        let uu____27328 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27328  in
      let uu____27335 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____27335
      then
        let uu____27336 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____27336 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____27342  ->
                 let uu____27343 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____27343)
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
            ((let uu____27364 =
                let uu____27369 =
                  let uu____27370 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27370
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27369)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27364);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____27385 = config [AllowUnboundUniverses] env  in
          norm_comp uu____27385 [] c
        with
        | e ->
            ((let uu____27398 =
                let uu____27403 =
                  let uu____27404 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27404
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27403)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27398);
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
                   let uu____27449 =
                     let uu____27450 =
                       let uu____27457 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27457)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27450  in
                   mk uu____27449 t01.FStar_Syntax_Syntax.pos
               | uu____27462 -> t2)
          | uu____27463 -> t2  in
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
        let uu____27527 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27527 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27556 ->
                 let uu____27563 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27563 with
                  | (actuals,uu____27573,uu____27574) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27588 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27588 with
                         | (binders,args) ->
                             let uu____27599 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27599
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
      | uu____27613 ->
          let uu____27614 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27614 with
           | (head1,args) ->
               let uu____27651 =
                 let uu____27652 = FStar_Syntax_Subst.compress head1  in
                 uu____27652.FStar_Syntax_Syntax.n  in
               (match uu____27651 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27677 =
                      let uu____27690 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27690  in
                    (match uu____27677 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27720 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___229_27728 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___229_27728.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___229_27728.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___229_27728.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___229_27728.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___229_27728.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___229_27728.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___229_27728.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___229_27728.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___229_27728.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___229_27728.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___229_27728.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___229_27728.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___229_27728.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___229_27728.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___229_27728.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___229_27728.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___229_27728.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___229_27728.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___229_27728.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___229_27728.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___229_27728.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___229_27728.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___229_27728.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___229_27728.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___229_27728.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___229_27728.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___229_27728.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___229_27728.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___229_27728.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___229_27728.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___229_27728.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___229_27728.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___229_27728.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___229_27728.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___229_27728.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___229_27728.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____27720 with
                            | (uu____27729,ty,uu____27731) ->
                                eta_expand_with_type env t ty))
                | uu____27732 ->
                    let uu____27733 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___230_27741 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___230_27741.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___230_27741.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___230_27741.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___230_27741.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___230_27741.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___230_27741.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___230_27741.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___230_27741.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___230_27741.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___230_27741.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___230_27741.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___230_27741.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___230_27741.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___230_27741.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___230_27741.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___230_27741.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___230_27741.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___230_27741.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___230_27741.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___230_27741.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___230_27741.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___230_27741.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___230_27741.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___230_27741.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___230_27741.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___230_27741.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___230_27741.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___230_27741.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___230_27741.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___230_27741.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___230_27741.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___230_27741.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___230_27741.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___230_27741.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___230_27741.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___230_27741.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____27733 with
                     | (uu____27742,ty,uu____27744) ->
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
      let uu___231_27817 = x  in
      let uu____27818 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___231_27817.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___231_27817.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27818
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27821 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27846 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27847 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27848 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27849 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27856 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27857 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27858 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___232_27888 = rc  in
          let uu____27889 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27898 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___232_27888.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27889;
            FStar_Syntax_Syntax.residual_flags = uu____27898
          }  in
        let uu____27901 =
          let uu____27902 =
            let uu____27919 = elim_delayed_subst_binders bs  in
            let uu____27926 = elim_delayed_subst_term t2  in
            let uu____27929 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27919, uu____27926, uu____27929)  in
          FStar_Syntax_Syntax.Tm_abs uu____27902  in
        mk1 uu____27901
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27960 =
          let uu____27961 =
            let uu____27974 = elim_delayed_subst_binders bs  in
            let uu____27981 = elim_delayed_subst_comp c  in
            (uu____27974, uu____27981)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27961  in
        mk1 uu____27960
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27998 =
          let uu____27999 =
            let uu____28006 = elim_bv bv  in
            let uu____28007 = elim_delayed_subst_term phi  in
            (uu____28006, uu____28007)  in
          FStar_Syntax_Syntax.Tm_refine uu____27999  in
        mk1 uu____27998
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28034 =
          let uu____28035 =
            let uu____28050 = elim_delayed_subst_term t2  in
            let uu____28053 = elim_delayed_subst_args args  in
            (uu____28050, uu____28053)  in
          FStar_Syntax_Syntax.Tm_app uu____28035  in
        mk1 uu____28034
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___233_28121 = p  in
              let uu____28122 =
                let uu____28123 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28123  in
              {
                FStar_Syntax_Syntax.v = uu____28122;
                FStar_Syntax_Syntax.p =
                  (uu___233_28121.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___234_28125 = p  in
              let uu____28126 =
                let uu____28127 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28127  in
              {
                FStar_Syntax_Syntax.v = uu____28126;
                FStar_Syntax_Syntax.p =
                  (uu___234_28125.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___235_28134 = p  in
              let uu____28135 =
                let uu____28136 =
                  let uu____28143 = elim_bv x  in
                  let uu____28144 = elim_delayed_subst_term t0  in
                  (uu____28143, uu____28144)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28136  in
              {
                FStar_Syntax_Syntax.v = uu____28135;
                FStar_Syntax_Syntax.p =
                  (uu___235_28134.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___236_28167 = p  in
              let uu____28168 =
                let uu____28169 =
                  let uu____28182 =
                    FStar_List.map
                      (fun uu____28205  ->
                         match uu____28205 with
                         | (x,b) ->
                             let uu____28218 = elim_pat x  in
                             (uu____28218, b)) pats
                     in
                  (fv, uu____28182)  in
                FStar_Syntax_Syntax.Pat_cons uu____28169  in
              {
                FStar_Syntax_Syntax.v = uu____28168;
                FStar_Syntax_Syntax.p =
                  (uu___236_28167.FStar_Syntax_Syntax.p)
              }
          | uu____28231 -> p  in
        let elim_branch uu____28255 =
          match uu____28255 with
          | (pat,wopt,t3) ->
              let uu____28281 = elim_pat pat  in
              let uu____28284 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28287 = elim_delayed_subst_term t3  in
              (uu____28281, uu____28284, uu____28287)
           in
        let uu____28292 =
          let uu____28293 =
            let uu____28316 = elim_delayed_subst_term t2  in
            let uu____28319 = FStar_List.map elim_branch branches  in
            (uu____28316, uu____28319)  in
          FStar_Syntax_Syntax.Tm_match uu____28293  in
        mk1 uu____28292
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28450 =
          match uu____28450 with
          | (tc,topt) ->
              let uu____28485 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28495 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28495
                | FStar_Util.Inr c ->
                    let uu____28497 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28497
                 in
              let uu____28498 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28485, uu____28498)
           in
        let uu____28507 =
          let uu____28508 =
            let uu____28535 = elim_delayed_subst_term t2  in
            let uu____28538 = elim_ascription a  in
            (uu____28535, uu____28538, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28508  in
        mk1 uu____28507
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___237_28599 = lb  in
          let uu____28600 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28603 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___237_28599.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___237_28599.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28600;
            FStar_Syntax_Syntax.lbeff =
              (uu___237_28599.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28603;
            FStar_Syntax_Syntax.lbattrs =
              (uu___237_28599.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___237_28599.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28606 =
          let uu____28607 =
            let uu____28620 =
              let uu____28627 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28627)  in
            let uu____28636 = elim_delayed_subst_term t2  in
            (uu____28620, uu____28636)  in
          FStar_Syntax_Syntax.Tm_let uu____28607  in
        mk1 uu____28606
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28686 =
          let uu____28687 =
            let uu____28694 = elim_delayed_subst_term tm  in
            (uu____28694, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28687  in
        mk1 uu____28686
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28705 =
          let uu____28706 =
            let uu____28713 = elim_delayed_subst_term t2  in
            let uu____28716 = elim_delayed_subst_meta md  in
            (uu____28713, uu____28716)  in
          FStar_Syntax_Syntax.Tm_meta uu____28706  in
        mk1 uu____28705

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___119_28725  ->
         match uu___119_28725 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28729 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28729
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
        let uu____28752 =
          let uu____28753 =
            let uu____28762 = elim_delayed_subst_term t  in
            (uu____28762, uopt)  in
          FStar_Syntax_Syntax.Total uu____28753  in
        mk1 uu____28752
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28779 =
          let uu____28780 =
            let uu____28789 = elim_delayed_subst_term t  in
            (uu____28789, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28780  in
        mk1 uu____28779
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___238_28798 = ct  in
          let uu____28799 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28802 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28811 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___238_28798.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___238_28798.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28799;
            FStar_Syntax_Syntax.effect_args = uu____28802;
            FStar_Syntax_Syntax.flags = uu____28811
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___120_28814  ->
    match uu___120_28814 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____28826 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____28826
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28859 =
          let uu____28866 = elim_delayed_subst_term t  in (m, uu____28866)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28859
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28878 =
          let uu____28887 = elim_delayed_subst_term t  in
          (m1, m2, uu____28887)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28878
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____28914  ->
         match uu____28914 with
         | (t,q) ->
             let uu____28925 = elim_delayed_subst_term t  in (uu____28925, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28945  ->
         match uu____28945 with
         | (x,q) ->
             let uu____28956 =
               let uu___239_28957 = x  in
               let uu____28958 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___239_28957.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___239_28957.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28958
               }  in
             (uu____28956, q)) bs

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
            | (uu____29050,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29076,FStar_Util.Inl t) ->
                let uu____29094 =
                  let uu____29101 =
                    let uu____29102 =
                      let uu____29115 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29115)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29102  in
                  FStar_Syntax_Syntax.mk uu____29101  in
                uu____29094 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29129 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29129 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29159 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29222 ->
                    let uu____29223 =
                      let uu____29232 =
                        let uu____29233 = FStar_Syntax_Subst.compress t4  in
                        uu____29233.FStar_Syntax_Syntax.n  in
                      (uu____29232, tc)  in
                    (match uu____29223 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29260) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29301) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29340,FStar_Util.Inl uu____29341) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29364 -> failwith "Impossible")
                 in
              (match uu____29159 with
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
          let uu____29489 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29489 with
          | (univ_names1,binders1,tc) ->
              let uu____29555 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29555)
  
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
          let uu____29604 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29604 with
          | (univ_names1,binders1,tc) ->
              let uu____29670 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29670)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29709 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29709 with
           | (univ_names1,binders1,typ1) ->
               let uu___240_29743 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_29743.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_29743.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_29743.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_29743.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___241_29758 = s  in
          let uu____29759 =
            let uu____29760 =
              let uu____29769 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29769, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29760  in
          {
            FStar_Syntax_Syntax.sigel = uu____29759;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_29758.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_29758.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_29758.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_29758.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29786 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29786 with
           | (univ_names1,uu____29806,typ1) ->
               let uu___242_29824 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_29824.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_29824.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_29824.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_29824.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29830 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29830 with
           | (univ_names1,uu____29850,typ1) ->
               let uu___243_29868 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_29868.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_29868.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_29868.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_29868.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29896 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29896 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29921 =
                            let uu____29922 =
                              let uu____29923 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29923  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29922
                             in
                          elim_delayed_subst_term uu____29921  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___244_29926 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___244_29926.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___244_29926.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___244_29926.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___244_29926.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___245_29927 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___245_29927.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_29927.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_29927.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_29927.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___246_29933 = s  in
          let uu____29934 =
            let uu____29935 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29935  in
          {
            FStar_Syntax_Syntax.sigel = uu____29934;
            FStar_Syntax_Syntax.sigrng =
              (uu___246_29933.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_29933.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_29933.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_29933.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29939 = elim_uvars_aux_t env us [] t  in
          (match uu____29939 with
           | (us1,uu____29959,t1) ->
               let uu___247_29977 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___247_29977.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___247_29977.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___247_29977.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___247_29977.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____29978 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____29980 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____29980 with
           | (univs1,binders,signature) ->
               let uu____30014 =
                 let uu____30023 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30023 with
                 | (univs_opening,univs2) ->
                     let uu____30050 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30050)
                  in
               (match uu____30014 with
                | (univs_opening,univs_closing) ->
                    let uu____30067 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30073 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30074 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30073, uu____30074)  in
                    (match uu____30067 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30098 =
                           match uu____30098 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30116 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30116 with
                                | (us1,t1) ->
                                    let uu____30127 =
                                      let uu____30136 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30145 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30136, uu____30145)  in
                                    (match uu____30127 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30172 =
                                           let uu____30181 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____30190 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____30181, uu____30190)  in
                                         (match uu____30172 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30218 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30218
                                                 in
                                              let uu____30219 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30219 with
                                               | (uu____30242,uu____30243,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30262 =
                                                       let uu____30263 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30263
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30262
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30272 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30272 with
                           | (uu____30289,uu____30290,t1) -> t1  in
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
                             | uu____30364 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30389 =
                               let uu____30390 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30390.FStar_Syntax_Syntax.n  in
                             match uu____30389 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30449 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30480 =
                               let uu____30481 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30481.FStar_Syntax_Syntax.n  in
                             match uu____30480 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30502) ->
                                 let uu____30523 = destruct_action_body body
                                    in
                                 (match uu____30523 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30568 ->
                                 let uu____30569 = destruct_action_body t  in
                                 (match uu____30569 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30618 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30618 with
                           | (action_univs,t) ->
                               let uu____30627 = destruct_action_typ_templ t
                                  in
                               (match uu____30627 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___248_30668 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___248_30668.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___248_30668.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___249_30670 = ed  in
                           let uu____30671 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30672 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30673 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30674 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30675 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30676 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30677 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____30678 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____30679 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____30680 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30681 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____30682 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30683 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30684 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___249_30670.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___249_30670.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____30671;
                             FStar_Syntax_Syntax.bind_wp = uu____30672;
                             FStar_Syntax_Syntax.if_then_else = uu____30673;
                             FStar_Syntax_Syntax.ite_wp = uu____30674;
                             FStar_Syntax_Syntax.stronger = uu____30675;
                             FStar_Syntax_Syntax.close_wp = uu____30676;
                             FStar_Syntax_Syntax.assert_p = uu____30677;
                             FStar_Syntax_Syntax.assume_p = uu____30678;
                             FStar_Syntax_Syntax.null_wp = uu____30679;
                             FStar_Syntax_Syntax.trivial = uu____30680;
                             FStar_Syntax_Syntax.repr = uu____30681;
                             FStar_Syntax_Syntax.return_repr = uu____30682;
                             FStar_Syntax_Syntax.bind_repr = uu____30683;
                             FStar_Syntax_Syntax.actions = uu____30684;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___249_30670.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___250_30687 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___250_30687.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___250_30687.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___250_30687.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___250_30687.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___121_30708 =
            match uu___121_30708 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30739 = elim_uvars_aux_t env us [] t  in
                (match uu____30739 with
                 | (us1,uu____30767,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___251_30794 = sub_eff  in
            let uu____30795 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30798 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___251_30794.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___251_30794.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30795;
              FStar_Syntax_Syntax.lift = uu____30798
            }  in
          let uu___252_30801 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___252_30801.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___252_30801.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___252_30801.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___252_30801.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____30811 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30811 with
           | (univ_names1,binders1,comp1) ->
               let uu___253_30845 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___253_30845.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___253_30845.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___253_30845.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___253_30845.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30848 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30849 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  