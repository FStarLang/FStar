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
  fun uu___104_3222  ->
    match uu___104_3222 with
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
  fun uu___105_3284  ->
    match uu___105_3284 with
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
  fun uu___106_3404  ->
    match uu___106_3404 with | [] -> true | uu____3407 -> false
  
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
            (fun uu____3884  ->
               let uu____3885 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3886 = env_to_string env  in
               let uu____3887 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3885 uu____3886 uu____3887);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3896 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3899 ->
                    let uu____3924 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3924
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3925 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3926 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3927 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3928 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3956 ->
                           let uu____3971 =
                             let uu____3972 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3973 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3972 uu____3973
                              in
                           failwith uu____3971
                       | uu____3976 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___107_4013  ->
                                         match uu___107_4013 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4020 =
                                               let uu____4027 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4027)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4020
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___151_4037 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___151_4037.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___151_4037.FStar_Syntax_Syntax.sort)
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
                                              | uu____4042 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4045 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___152_4049 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___152_4049.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___152_4049.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4076 =
                        let uu____4077 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4077  in
                      mk uu____4076 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4085 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4085  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4087 = lookup_bvar env x  in
                    (match uu____4087 with
                     | Univ uu____4090 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___153_4094 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___153_4094.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___153_4094.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4100,uu____4101) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4186  ->
                              fun stack1  ->
                                match uu____4186 with
                                | (a,aq) ->
                                    let uu____4198 =
                                      let uu____4199 =
                                        let uu____4206 =
                                          let uu____4207 =
                                            let uu____4238 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4238, false)  in
                                          Clos uu____4207  in
                                        (uu____4206, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4199  in
                                    uu____4198 :: stack1) args)
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
                    let uu____4414 = close_binders cfg env bs  in
                    (match uu____4414 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4461 =
                      let uu____4472 =
                        let uu____4479 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4479]  in
                      close_binders cfg env uu____4472  in
                    (match uu____4461 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4514 =
                             let uu____4515 =
                               let uu____4522 =
                                 let uu____4523 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4523
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4522, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4515  in
                           mk uu____4514 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4614 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4614
                      | FStar_Util.Inr c ->
                          let uu____4628 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4628
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4647 =
                        let uu____4648 =
                          let uu____4675 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4675, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4648  in
                      mk uu____4647 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4721 =
                            let uu____4722 =
                              let uu____4729 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4729, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4722  in
                          mk uu____4721 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4781  -> dummy :: env1) env
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
                    let uu____4802 =
                      let uu____4813 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4813
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4832 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___154_4848 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_4848.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_4848.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4832))
                       in
                    (match uu____4802 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___155_4866 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_4866.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_4866.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___155_4866.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___155_4866.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4880,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4943  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4960 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4960
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4972  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4996 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4996
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___156_5004 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___156_5004.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___156_5004.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___157_5005 = lb  in
                      let uu____5006 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___157_5005.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___157_5005.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5006;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___157_5005.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___157_5005.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5038  -> fun env1  -> dummy :: env1)
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
            (fun uu____5127  ->
               let uu____5128 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5129 = env_to_string env  in
               let uu____5130 = stack_to_string stack  in
               let uu____5131 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5128 uu____5129 uu____5130 uu____5131);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5136,uu____5137),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5214 = close_binders cfg env' bs  in
               (match uu____5214 with
                | (bs1,uu____5228) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5244 =
                      let uu___158_5247 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___158_5247.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___158_5247.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5244)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5303 =
                 match uu____5303 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5418 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5447 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5531  ->
                                     fun uu____5532  ->
                                       match (uu____5531, uu____5532) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5671 = norm_pat env4 p1
                                              in
                                           (match uu____5671 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5447 with
                            | (pats1,env4) ->
                                ((let uu___159_5833 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___159_5833.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___160_5852 = x  in
                             let uu____5853 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_5852.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_5852.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5853
                             }  in
                           ((let uu___161_5867 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___161_5867.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___162_5878 = x  in
                             let uu____5879 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_5878.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_5878.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5879
                             }  in
                           ((let uu___163_5893 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___163_5893.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___164_5909 = x  in
                             let uu____5910 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___164_5909.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___164_5909.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5910
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___165_5927 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___165_5927.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5932 = norm_pat env2 pat  in
                     (match uu____5932 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6001 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6001
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6020 =
                   let uu____6021 =
                     let uu____6044 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6044)  in
                   FStar_Syntax_Syntax.Tm_match uu____6021  in
                 mk uu____6020 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6157 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6246  ->
                                       match uu____6246 with
                                       | (a,q) ->
                                           let uu____6265 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6265, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6157
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6276 =
                       let uu____6283 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6283)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6276
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6295 =
                       let uu____6304 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6304)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6295
                 | uu____6309 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6315 -> failwith "Impossible: unexpected stack element")

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
        let uu____6329 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6402  ->
                  fun uu____6403  ->
                    match (uu____6402, uu____6403) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_6521 = b  in
                          let uu____6522 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_6521.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_6521.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6522
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6329 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6639 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6652 = inline_closure_env cfg env [] t  in
                 let uu____6653 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6652 uu____6653
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6666 = inline_closure_env cfg env [] t  in
                 let uu____6667 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6666 uu____6667
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6711  ->
                           match uu____6711 with
                           | (a,q) ->
                               let uu____6724 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6724, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___108_6739  ->
                           match uu___108_6739 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6743 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6743
                           | f -> f))
                    in
                 let uu____6747 =
                   let uu___167_6748 = c1  in
                   let uu____6749 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6749;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_6748.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6747)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___109_6759  ->
            match uu___109_6759 with
            | FStar_Syntax_Syntax.DECREASES uu____6760 -> false
            | uu____6763 -> true))

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
                   (fun uu___110_6781  ->
                      match uu___110_6781 with
                      | FStar_Syntax_Syntax.DECREASES uu____6782 -> false
                      | uu____6785 -> true))
               in
            let rc1 =
              let uu___168_6787 = rc  in
              let uu____6788 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_6787.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6788;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6797 -> lopt

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
    let uu____6902 =
      let uu____6911 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6911  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6902  in
  let arg_as_bounded_int uu____6937 =
    match uu____6937 with
    | (a,uu____6949) ->
        let uu____6956 =
          let uu____6957 = FStar_Syntax_Subst.compress a  in
          uu____6957.FStar_Syntax_Syntax.n  in
        (match uu____6956 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6967;
                FStar_Syntax_Syntax.vars = uu____6968;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6970;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6971;_},uu____6972)::[])
             when
             let uu____7011 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7011 "int_to_t" ->
             let uu____7012 =
               let uu____7017 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7017)  in
             FStar_Pervasives_Native.Some uu____7012
         | uu____7022 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7070 = f a  in FStar_Pervasives_Native.Some uu____7070
    | uu____7071 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7127 = f a0 a1  in FStar_Pervasives_Native.Some uu____7127
    | uu____7128 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7186 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7186  in
  let binary_op as_a f res args =
    let uu____7257 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7257  in
  let as_primitive_step is_strong uu____7294 =
    match uu____7294 with
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
           let uu____7354 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7354)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7390 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7390)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7419 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7419)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7455 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7455)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7491 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7491)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7623 =
          let uu____7632 = as_a a  in
          let uu____7635 = as_b b  in (uu____7632, uu____7635)  in
        (match uu____7623 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7650 =
               let uu____7651 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7651  in
             FStar_Pervasives_Native.Some uu____7650
         | uu____7652 -> FStar_Pervasives_Native.None)
    | uu____7661 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7681 =
        let uu____7682 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7682  in
      mk uu____7681 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7696 =
      let uu____7699 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7699  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7696  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7741 =
      let uu____7742 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7742  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7741
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7806 = arg_as_string a1  in
        (match uu____7806 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7812 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7812 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7825 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7825
              | uu____7826 -> FStar_Pervasives_Native.None)
         | uu____7831 -> FStar_Pervasives_Native.None)
    | uu____7834 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7854 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7854
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7891 =
          let uu____7912 = arg_as_string fn  in
          let uu____7915 = arg_as_int from_line  in
          let uu____7918 = arg_as_int from_col  in
          let uu____7921 = arg_as_int to_line  in
          let uu____7924 = arg_as_int to_col  in
          (uu____7912, uu____7915, uu____7918, uu____7921, uu____7924)  in
        (match uu____7891 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7955 =
                 let uu____7956 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7957 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7956 uu____7957  in
               let uu____7958 =
                 let uu____7959 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7960 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7959 uu____7960  in
               FStar_Range.mk_range fn1 uu____7955 uu____7958  in
             let uu____7961 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7961
         | uu____7962 -> FStar_Pervasives_Native.None)
    | uu____7983 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8016)::(a1,uu____8018)::(a2,uu____8020)::[] ->
        let uu____8057 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8057 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8062 -> FStar_Pervasives_Native.None)
    | uu____8063 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8094)::[] ->
        let uu____8103 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8103 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8109 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8109
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8110 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8136 =
      let uu____8153 =
        let uu____8170 =
          let uu____8187 =
            let uu____8204 =
              let uu____8221 =
                let uu____8238 =
                  let uu____8255 =
                    let uu____8272 =
                      let uu____8289 =
                        let uu____8306 =
                          let uu____8323 =
                            let uu____8340 =
                              let uu____8357 =
                                let uu____8374 =
                                  let uu____8391 =
                                    let uu____8408 =
                                      let uu____8425 =
                                        let uu____8442 =
                                          let uu____8459 =
                                            let uu____8476 =
                                              let uu____8493 =
                                                let uu____8508 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8508,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8517 =
                                                let uu____8534 =
                                                  let uu____8549 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8549,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8562 =
                                                  let uu____8579 =
                                                    let uu____8594 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8594,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8603 =
                                                    let uu____8620 =
                                                      let uu____8635 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8635,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8620]  in
                                                  uu____8579 :: uu____8603
                                                   in
                                                uu____8534 :: uu____8562  in
                                              uu____8493 :: uu____8517  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8476
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8459
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8442
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8425
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8408
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8855 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8855 y)))
                                    :: uu____8391
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8374
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8357
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8340
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8323
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8306
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8289
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9050 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9050)))
                      :: uu____8272
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9080 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9080)))
                    :: uu____8255
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9110 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9110)))
                  :: uu____8238
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9140 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9140)))
                :: uu____8221
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8204
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8187
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8170
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8153
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8136
     in
  let weak_ops =
    let uu____9295 =
      let uu____9310 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9310, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9295]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9390 =
        let uu____9395 =
          let uu____9396 = FStar_Syntax_Syntax.as_arg c  in [uu____9396]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9395  in
      uu____9390 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9470 =
                let uu____9485 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9485, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9507  ->
                          fun uu____9508  ->
                            match (uu____9507, uu____9508) with
                            | ((int_to_t1,x),(uu____9527,y)) ->
                                let uu____9537 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9537)))
                 in
              let uu____9538 =
                let uu____9555 =
                  let uu____9570 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9570, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9592  ->
                            fun uu____9593  ->
                              match (uu____9592, uu____9593) with
                              | ((int_to_t1,x),(uu____9612,y)) ->
                                  let uu____9622 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9622)))
                   in
                let uu____9623 =
                  let uu____9640 =
                    let uu____9655 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9655, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9677  ->
                              fun uu____9678  ->
                                match (uu____9677, uu____9678) with
                                | ((int_to_t1,x),(uu____9697,y)) ->
                                    let uu____9707 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9707)))
                     in
                  let uu____9708 =
                    let uu____9725 =
                      let uu____9740 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9740, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9758  ->
                                match uu____9758 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9725]  in
                  uu____9640 :: uu____9708  in
                uu____9555 :: uu____9623  in
              uu____9470 :: uu____9538))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9888 =
                let uu____9903 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9903, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9925  ->
                          fun uu____9926  ->
                            match (uu____9925, uu____9926) with
                            | ((int_to_t1,x),(uu____9945,y)) ->
                                let uu____9955 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9955)))
                 in
              let uu____9956 =
                let uu____9973 =
                  let uu____9988 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9988, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10010  ->
                            fun uu____10011  ->
                              match (uu____10010, uu____10011) with
                              | ((int_to_t1,x),(uu____10030,y)) ->
                                  let uu____10040 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10040)))
                   in
                [uu____9973]  in
              uu____9888 :: uu____9956))
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
    | (_typ,uu____10170)::(a1,uu____10172)::(a2,uu____10174)::[] ->
        let uu____10211 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10211 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10215 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10215.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10215.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10217 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10217.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10217.FStar_Syntax_Syntax.vars)
                })
         | uu____10218 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10220)::uu____10221::(a1,uu____10223)::(a2,uu____10225)::[]
        ->
        let uu____10274 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10274 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10278 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10278.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10278.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10280 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10280.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10280.FStar_Syntax_Syntax.vars)
                })
         | uu____10281 -> FStar_Pervasives_Native.None)
    | uu____10282 -> failwith "Unexpected number of arguments"  in
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
    let uu____10336 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10336 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10388 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10388) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10450  ->
           fun subst1  ->
             match uu____10450 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10491,uu____10492)) ->
                      let uu____10551 = b  in
                      (match uu____10551 with
                       | (bv,uu____10559) ->
                           let uu____10560 =
                             let uu____10561 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10561  in
                           if uu____10560
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10566 = unembed_binder term1  in
                              match uu____10566 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10573 =
                                      let uu___171_10574 = bv  in
                                      let uu____10575 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___171_10574.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___171_10574.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10575
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10573
                                     in
                                  let b_for_x =
                                    let uu____10579 =
                                      let uu____10586 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10586)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10579  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___111_10600  ->
                                         match uu___111_10600 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10601,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10603;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10604;_})
                                             ->
                                             let uu____10609 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10609
                                         | uu____10610 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10611 -> subst1)) env []
  
let reduce_primops :
  'Auu____10634 'Auu____10635 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10634) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10635 ->
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
            (let uu____10683 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10683 with
             | (head1,args) ->
                 let uu____10722 =
                   let uu____10723 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10723.FStar_Syntax_Syntax.n  in
                 (match uu____10722 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10729 = find_prim_step cfg fv  in
                      (match uu____10729 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10755  ->
                                   let uu____10756 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10757 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10764 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10756 uu____10757 uu____10764);
                              tm)
                           else
                             (let uu____10766 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10766 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10879  ->
                                        let uu____10880 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10880);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10883  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10885 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10885 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10893  ->
                                              let uu____10894 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10894);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10900  ->
                                              let uu____10901 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10902 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10901 uu____10902);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10903 ->
                           (log_primops cfg
                              (fun uu____10907  ->
                                 let uu____10908 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10908);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10912  ->
                            let uu____10913 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10913);
                       (match args with
                        | (a1,uu____10917)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10934 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10946  ->
                            let uu____10947 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10947);
                       (match args with
                        | (t,uu____10951)::(r,uu____10953)::[] ->
                            let uu____10980 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10980 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10986 -> tm))
                  | uu____10995 -> tm))
  
let reduce_equality :
  'Auu____11006 'Auu____11007 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11006) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11007 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_11053 = cfg  in
         {
           steps =
             (let uu___173_11056 = default_steps  in
              {
                beta = (uu___173_11056.beta);
                iota = (uu___173_11056.iota);
                zeta = (uu___173_11056.zeta);
                weak = (uu___173_11056.weak);
                hnf = (uu___173_11056.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___173_11056.do_not_unfold_pure_lets);
                unfold_until = (uu___173_11056.unfold_until);
                unfold_only = (uu___173_11056.unfold_only);
                unfold_fully = (uu___173_11056.unfold_fully);
                unfold_attr = (uu___173_11056.unfold_attr);
                unfold_tac = (uu___173_11056.unfold_tac);
                pure_subterms_within_computations =
                  (uu___173_11056.pure_subterms_within_computations);
                simplify = (uu___173_11056.simplify);
                erase_universes = (uu___173_11056.erase_universes);
                allow_unbound_universes =
                  (uu___173_11056.allow_unbound_universes);
                reify_ = (uu___173_11056.reify_);
                compress_uvars = (uu___173_11056.compress_uvars);
                no_full_norm = (uu___173_11056.no_full_norm);
                check_no_uvars = (uu___173_11056.check_no_uvars);
                unmeta = (uu___173_11056.unmeta);
                unascribe = (uu___173_11056.unascribe);
                in_full_norm_request = (uu___173_11056.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___173_11056.weakly_reduce_scrutinee)
              });
           tcenv = (uu___172_11053.tcenv);
           debug = (uu___172_11053.debug);
           delta_level = (uu___172_11053.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___172_11053.strong);
           memoize_lazy = (uu___172_11053.memoize_lazy);
           normalize_pure_lets = (uu___172_11053.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11063 .
    FStar_Syntax_Syntax.term -> 'Auu____11063 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11078 =
        let uu____11085 =
          let uu____11086 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11086.FStar_Syntax_Syntax.n  in
        (uu____11085, args)  in
      match uu____11078 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11092::uu____11093::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11097::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11102::uu____11103::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11106 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___112_11119  ->
    match uu___112_11119 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11125 =
          let uu____11128 =
            let uu____11129 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11129  in
          [uu____11128]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11125
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11135 =
          let uu____11138 =
            let uu____11139 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11139  in
          [uu____11138]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11135
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11162 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11162)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11213 =
            let uu____11218 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11218 s  in
          match uu____11213 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11234 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11234
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11260::(tm,uu____11262)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11291)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11312)::uu____11313::(tm,uu____11315)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11356 =
              let uu____11361 = full_norm steps  in parse_steps uu____11361
               in
            (match uu____11356 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11400 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___113_11419  ->
    match uu___113_11419 with
    | (App
        (uu____11422,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11423;
                       FStar_Syntax_Syntax.vars = uu____11424;_},uu____11425,uu____11426))::uu____11427
        -> true
    | uu____11432 -> false
  
let firstn :
  'Auu____11441 .
    Prims.int ->
      'Auu____11441 Prims.list ->
        ('Auu____11441 Prims.list,'Auu____11441 Prims.list)
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
          (uu____11483,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11484;
                         FStar_Syntax_Syntax.vars = uu____11485;_},uu____11486,uu____11487))::uu____11488
          -> (cfg.steps).reify_
      | uu____11493 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11516) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11526) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11545  ->
                  match uu____11545 with
                  | (a,uu____11553) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11559 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11584 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11585 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11600 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11601 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11602 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11603 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11604 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11605 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11612 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11619 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11632 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11649 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11662 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11669 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11731  ->
                   match uu____11731 with
                   | (a,uu____11739) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11746) ->
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
                     (fun uu____11868  ->
                        match uu____11868 with
                        | (a,uu____11876) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11881,uu____11882,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11888,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11894 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11901 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11902 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12194 ->
                   let uu____12219 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12219
               | uu____12220 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12228  ->
               let uu____12229 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12230 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12231 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12238 =
                 let uu____12239 =
                   let uu____12242 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12242
                    in
                 stack_to_string uu____12239  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12229 uu____12230 uu____12231 uu____12238);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12265 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12266 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12267 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12268;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____12269;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12272;
                 FStar_Syntax_Syntax.fv_delta = uu____12273;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12274;
                 FStar_Syntax_Syntax.fv_delta = uu____12275;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12276);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12283 ->
               let uu____12290 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12290
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12320 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12320)
               ->
               let cfg' =
                 let uu___174_12322 = cfg  in
                 {
                   steps =
                     (let uu___175_12325 = cfg.steps  in
                      {
                        beta = (uu___175_12325.beta);
                        iota = (uu___175_12325.iota);
                        zeta = (uu___175_12325.zeta);
                        weak = (uu___175_12325.weak);
                        hnf = (uu___175_12325.hnf);
                        primops = (uu___175_12325.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___175_12325.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___175_12325.unfold_attr);
                        unfold_tac = (uu___175_12325.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___175_12325.pure_subterms_within_computations);
                        simplify = (uu___175_12325.simplify);
                        erase_universes = (uu___175_12325.erase_universes);
                        allow_unbound_universes =
                          (uu___175_12325.allow_unbound_universes);
                        reify_ = (uu___175_12325.reify_);
                        compress_uvars = (uu___175_12325.compress_uvars);
                        no_full_norm = (uu___175_12325.no_full_norm);
                        check_no_uvars = (uu___175_12325.check_no_uvars);
                        unmeta = (uu___175_12325.unmeta);
                        unascribe = (uu___175_12325.unascribe);
                        in_full_norm_request =
                          (uu___175_12325.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___175_12325.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___174_12322.tcenv);
                   debug = (uu___174_12322.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___174_12322.primitive_steps);
                   strong = (uu___174_12322.strong);
                   memoize_lazy = (uu___174_12322.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12330 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____12330 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12359  ->
                              fun stack1  ->
                                match uu____12359 with
                                | (a,aq) ->
                                    let uu____12371 =
                                      let uu____12372 =
                                        let uu____12379 =
                                          let uu____12380 =
                                            let uu____12411 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12411, false)  in
                                          Clos uu____12380  in
                                        (uu____12379, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12372  in
                                    uu____12371 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12499  ->
                          let uu____12500 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12500);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12522 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___114_12527  ->
                                match uu___114_12527 with
                                | UnfoldUntil uu____12528 -> true
                                | UnfoldOnly uu____12529 -> true
                                | UnfoldFully uu____12532 -> true
                                | uu____12535 -> false))
                         in
                      if uu____12522
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___176_12540 = cfg  in
                      let uu____12541 =
                        let uu___177_12542 = to_fsteps s  in
                        {
                          beta = (uu___177_12542.beta);
                          iota = (uu___177_12542.iota);
                          zeta = (uu___177_12542.zeta);
                          weak = (uu___177_12542.weak);
                          hnf = (uu___177_12542.hnf);
                          primops = (uu___177_12542.primops);
                          do_not_unfold_pure_lets =
                            (uu___177_12542.do_not_unfold_pure_lets);
                          unfold_until = (uu___177_12542.unfold_until);
                          unfold_only = (uu___177_12542.unfold_only);
                          unfold_fully = (uu___177_12542.unfold_fully);
                          unfold_attr = (uu___177_12542.unfold_attr);
                          unfold_tac = (uu___177_12542.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___177_12542.pure_subterms_within_computations);
                          simplify = (uu___177_12542.simplify);
                          erase_universes = (uu___177_12542.erase_universes);
                          allow_unbound_universes =
                            (uu___177_12542.allow_unbound_universes);
                          reify_ = (uu___177_12542.reify_);
                          compress_uvars = (uu___177_12542.compress_uvars);
                          no_full_norm = (uu___177_12542.no_full_norm);
                          check_no_uvars = (uu___177_12542.check_no_uvars);
                          unmeta = (uu___177_12542.unmeta);
                          unascribe = (uu___177_12542.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___177_12542.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12541;
                        tcenv = (uu___176_12540.tcenv);
                        debug = (uu___176_12540.debug);
                        delta_level;
                        primitive_steps = (uu___176_12540.primitive_steps);
                        strong = (uu___176_12540.strong);
                        memoize_lazy = (uu___176_12540.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12547 =
                          let uu____12548 =
                            let uu____12553 = FStar_Util.now ()  in
                            (t1, uu____12553)  in
                          Debug uu____12548  in
                        uu____12547 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12557 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12557
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12566 =
                      let uu____12573 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12573, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12566  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12583 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12583  in
               let uu____12584 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12584
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12590  ->
                       let uu____12591 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12592 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12591 uu____12592);
                  if b
                  then
                    (let uu____12593 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12593 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12601 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12601) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12614),uu____12615);
                                FStar_Syntax_Syntax.sigrng = uu____12616;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12618;
                                FStar_Syntax_Syntax.sigattrs = uu____12619;_},uu____12620),uu____12621)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12680 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___115_12684  ->
                               match uu___115_12684 with
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
                          (let uu____12694 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12694))
                         &&
                         (match (((cfg.steps).unfold_only),
                                  ((cfg.steps).unfold_attr))
                          with
                          | (FStar_Pervasives_Native.Some
                             lids,FStar_Pervasives_Native.Some ats') ->
                              (FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                                ||
                                ((match attrs with
                                  | FStar_Pervasives_Native.Some ats ->
                                      FStar_Util.for_some
                                        (fun at  ->
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq at)
                                             ats') ats
                                  | FStar_Pervasives_Native.None  -> true))
                          | (FStar_Pervasives_Native.Some
                             lids,FStar_Pervasives_Native.None ) ->
                              FStar_Util.for_some
                                (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                          | (FStar_Pervasives_Native.None
                             ,FStar_Pervasives_Native.Some ats') ->
                              (match attrs with
                               | FStar_Pervasives_Native.Some ats ->
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats')
                                     ats
                               | FStar_Pervasives_Native.None  -> true)
                          | (FStar_Pervasives_Native.None
                             ,FStar_Pervasives_Native.None ) -> true))
                     in
                  let uu____12786 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12802 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12802 then (true, true) else (false, false)
                     in
                  match uu____12786 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12815  ->
                            let uu____12816 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12817 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12818 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12816 uu____12817 uu____12818);
                       if should_delta2
                       then
                         (let uu____12819 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___178_12835 = cfg  in
                                 {
                                   steps =
                                     (let uu___179_12838 = cfg.steps  in
                                      {
                                        beta = (uu___179_12838.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___179_12838.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___179_12838.unfold_attr);
                                        unfold_tac =
                                          (uu___179_12838.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___179_12838.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___179_12838.erase_universes);
                                        allow_unbound_universes =
                                          (uu___179_12838.allow_unbound_universes);
                                        reify_ = (uu___179_12838.reify_);
                                        compress_uvars =
                                          (uu___179_12838.compress_uvars);
                                        no_full_norm =
                                          (uu___179_12838.no_full_norm);
                                        check_no_uvars =
                                          (uu___179_12838.check_no_uvars);
                                        unmeta = (uu___179_12838.unmeta);
                                        unascribe =
                                          (uu___179_12838.unascribe);
                                        in_full_norm_request =
                                          (uu___179_12838.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___179_12838.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___178_12835.tcenv);
                                   debug = (uu___178_12835.debug);
                                   delta_level = (uu___178_12835.delta_level);
                                   primitive_steps =
                                     (uu___178_12835.primitive_steps);
                                   strong = (uu___178_12835.strong);
                                   memoize_lazy =
                                     (uu___178_12835.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___178_12835.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12819 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12854 = lookup_bvar env x  in
               (match uu____12854 with
                | Univ uu____12855 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12904 = FStar_ST.op_Bang r  in
                      (match uu____12904 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____13026  ->
                                 let uu____13027 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____13028 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____13027
                                   uu____13028);
                            (let uu____13029 = maybe_weakly_reduced t'  in
                             if uu____13029
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____13030 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13101)::uu____13102 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____13112,uu____13113))::stack_rest ->
                    (match c with
                     | Univ uu____13117 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13126 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13147  ->
                                    let uu____13148 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13148);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13176  ->
                                    let uu____13177 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13177);
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
                       (fun uu____13243  ->
                          let uu____13244 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13244);
                     norm cfg env stack1 t1)
                | (Match uu____13245)::uu____13246 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13260 = cfg.steps  in
                             {
                               beta = (uu___180_13260.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13260.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13260.unfold_until);
                               unfold_only = (uu___180_13260.unfold_only);
                               unfold_fully = (uu___180_13260.unfold_fully);
                               unfold_attr = (uu___180_13260.unfold_attr);
                               unfold_tac = (uu___180_13260.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13260.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13260.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13260.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13260.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13260.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13260.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13262 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13262.tcenv);
                               debug = (uu___181_13262.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13262.primitive_steps);
                               strong = (uu___181_13262.strong);
                               memoize_lazy = (uu___181_13262.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13262.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13264 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13264 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13296  -> dummy :: env1) env)
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
                                          let uu____13337 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13337)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13344 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13344.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13344.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13345 -> lopt  in
                           (log cfg
                              (fun uu____13351  ->
                                 let uu____13352 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13352);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13361 = cfg  in
                               {
                                 steps = (uu___183_13361.steps);
                                 tcenv = (uu___183_13361.tcenv);
                                 debug = (uu___183_13361.debug);
                                 delta_level = (uu___183_13361.delta_level);
                                 primitive_steps =
                                   (uu___183_13361.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13361.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13361.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____13364)::uu____13365 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13375 = cfg.steps  in
                             {
                               beta = (uu___180_13375.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13375.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13375.unfold_until);
                               unfold_only = (uu___180_13375.unfold_only);
                               unfold_fully = (uu___180_13375.unfold_fully);
                               unfold_attr = (uu___180_13375.unfold_attr);
                               unfold_tac = (uu___180_13375.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13375.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13375.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13375.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13375.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13375.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13375.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13377 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13377.tcenv);
                               debug = (uu___181_13377.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13377.primitive_steps);
                               strong = (uu___181_13377.strong);
                               memoize_lazy = (uu___181_13377.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13377.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13379 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13379 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13411  -> dummy :: env1) env)
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
                                          let uu____13452 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13452)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13459 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13459.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13459.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13460 -> lopt  in
                           (log cfg
                              (fun uu____13466  ->
                                 let uu____13467 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13467);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13476 = cfg  in
                               {
                                 steps = (uu___183_13476.steps);
                                 tcenv = (uu___183_13476.tcenv);
                                 debug = (uu___183_13476.debug);
                                 delta_level = (uu___183_13476.delta_level);
                                 primitive_steps =
                                   (uu___183_13476.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13476.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13476.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13479)::uu____13480 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13492 = cfg.steps  in
                             {
                               beta = (uu___180_13492.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13492.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13492.unfold_until);
                               unfold_only = (uu___180_13492.unfold_only);
                               unfold_fully = (uu___180_13492.unfold_fully);
                               unfold_attr = (uu___180_13492.unfold_attr);
                               unfold_tac = (uu___180_13492.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13492.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13492.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13492.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13492.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13492.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13492.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13494 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13494.tcenv);
                               debug = (uu___181_13494.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13494.primitive_steps);
                               strong = (uu___181_13494.strong);
                               memoize_lazy = (uu___181_13494.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13494.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13496 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13496 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13528  -> dummy :: env1) env)
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
                                          let uu____13569 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13569)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13576 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13576.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13576.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13577 -> lopt  in
                           (log cfg
                              (fun uu____13583  ->
                                 let uu____13584 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13584);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13593 = cfg  in
                               {
                                 steps = (uu___183_13593.steps);
                                 tcenv = (uu___183_13593.tcenv);
                                 debug = (uu___183_13593.debug);
                                 delta_level = (uu___183_13593.delta_level);
                                 primitive_steps =
                                   (uu___183_13593.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13593.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13593.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13596)::uu____13597 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13611 = cfg.steps  in
                             {
                               beta = (uu___180_13611.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13611.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13611.unfold_until);
                               unfold_only = (uu___180_13611.unfold_only);
                               unfold_fully = (uu___180_13611.unfold_fully);
                               unfold_attr = (uu___180_13611.unfold_attr);
                               unfold_tac = (uu___180_13611.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13611.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13611.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13611.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13611.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13611.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13611.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13613 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13613.tcenv);
                               debug = (uu___181_13613.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13613.primitive_steps);
                               strong = (uu___181_13613.strong);
                               memoize_lazy = (uu___181_13613.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13613.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13615 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13615 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13647  -> dummy :: env1) env)
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
                                          let uu____13688 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13688)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13695 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13695.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13695.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13696 -> lopt  in
                           (log cfg
                              (fun uu____13702  ->
                                 let uu____13703 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13703);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13712 = cfg  in
                               {
                                 steps = (uu___183_13712.steps);
                                 tcenv = (uu___183_13712.tcenv);
                                 debug = (uu___183_13712.debug);
                                 delta_level = (uu___183_13712.delta_level);
                                 primitive_steps =
                                   (uu___183_13712.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13712.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13712.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13715)::uu____13716 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13730 = cfg.steps  in
                             {
                               beta = (uu___180_13730.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13730.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13730.unfold_until);
                               unfold_only = (uu___180_13730.unfold_only);
                               unfold_fully = (uu___180_13730.unfold_fully);
                               unfold_attr = (uu___180_13730.unfold_attr);
                               unfold_tac = (uu___180_13730.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13730.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13730.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13730.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13730.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13730.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13730.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13732 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13732.tcenv);
                               debug = (uu___181_13732.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13732.primitive_steps);
                               strong = (uu___181_13732.strong);
                               memoize_lazy = (uu___181_13732.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13732.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13734 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13734 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13766  -> dummy :: env1) env)
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
                                          let uu____13807 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13807)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13814 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13814.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13814.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13815 -> lopt  in
                           (log cfg
                              (fun uu____13821  ->
                                 let uu____13822 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13822);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13831 = cfg  in
                               {
                                 steps = (uu___183_13831.steps);
                                 tcenv = (uu___183_13831.tcenv);
                                 debug = (uu___183_13831.debug);
                                 delta_level = (uu___183_13831.delta_level);
                                 primitive_steps =
                                   (uu___183_13831.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13831.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13831.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13834)::uu____13835 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13853 = cfg.steps  in
                             {
                               beta = (uu___180_13853.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13853.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13853.unfold_until);
                               unfold_only = (uu___180_13853.unfold_only);
                               unfold_fully = (uu___180_13853.unfold_fully);
                               unfold_attr = (uu___180_13853.unfold_attr);
                               unfold_tac = (uu___180_13853.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13853.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13853.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13853.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13853.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13853.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13853.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13855 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13855.tcenv);
                               debug = (uu___181_13855.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13855.primitive_steps);
                               strong = (uu___181_13855.strong);
                               memoize_lazy = (uu___181_13855.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13855.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13857 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13857 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13889  -> dummy :: env1) env)
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
                                          let uu____13930 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13930)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13937 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13937.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13937.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13938 -> lopt  in
                           (log cfg
                              (fun uu____13944  ->
                                 let uu____13945 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13945);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13954 = cfg  in
                               {
                                 steps = (uu___183_13954.steps);
                                 tcenv = (uu___183_13954.tcenv);
                                 debug = (uu___183_13954.debug);
                                 delta_level = (uu___183_13954.delta_level);
                                 primitive_steps =
                                   (uu___183_13954.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13954.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13954.normalize_pure_lets)
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
                             let uu___180_13960 = cfg.steps  in
                             {
                               beta = (uu___180_13960.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13960.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13960.unfold_until);
                               unfold_only = (uu___180_13960.unfold_only);
                               unfold_fully = (uu___180_13960.unfold_fully);
                               unfold_attr = (uu___180_13960.unfold_attr);
                               unfold_tac = (uu___180_13960.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13960.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13960.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13960.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13960.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13960.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13960.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13962 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13962.tcenv);
                               debug = (uu___181_13962.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13962.primitive_steps);
                               strong = (uu___181_13962.strong);
                               memoize_lazy = (uu___181_13962.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13962.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13964 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13964 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13996  -> dummy :: env1) env)
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
                                          let uu____14037 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14037)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14044 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14044.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14044.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14045 -> lopt  in
                           (log cfg
                              (fun uu____14051  ->
                                 let uu____14052 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14052);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14061 = cfg  in
                               {
                                 steps = (uu___183_14061.steps);
                                 tcenv = (uu___183_14061.tcenv);
                                 debug = (uu___183_14061.debug);
                                 delta_level = (uu___183_14061.delta_level);
                                 primitive_steps =
                                   (uu___183_14061.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14061.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14061.normalize_pure_lets)
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
                      (fun uu____14100  ->
                         fun stack1  ->
                           match uu____14100 with
                           | (a,aq) ->
                               let uu____14112 =
                                 let uu____14113 =
                                   let uu____14120 =
                                     let uu____14121 =
                                       let uu____14152 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____14152, false)  in
                                     Clos uu____14121  in
                                   (uu____14120, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____14113  in
                               uu____14112 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14240  ->
                     let uu____14241 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14241);
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
                             ((let uu___184_14287 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_14287.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_14287.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14288 ->
                      let uu____14303 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14303)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14306 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14306 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14331 =
                          let uu____14332 =
                            let uu____14339 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___185_14345 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___185_14345.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___185_14345.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14339)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14332  in
                        mk uu____14331 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14364 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14364
               else
                 (let uu____14366 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14366 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14374 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14396  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14374 c1  in
                      let t2 =
                        let uu____14418 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14418 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14529)::uu____14530 ->
                    (log cfg
                       (fun uu____14543  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14544)::uu____14545 ->
                    (log cfg
                       (fun uu____14556  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14557,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14558;
                                   FStar_Syntax_Syntax.vars = uu____14559;_},uu____14560,uu____14561))::uu____14562
                    ->
                    (log cfg
                       (fun uu____14569  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14570)::uu____14571 ->
                    (log cfg
                       (fun uu____14582  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14583 ->
                    (log cfg
                       (fun uu____14586  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14590  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14615 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14615
                         | FStar_Util.Inr c ->
                             let uu____14629 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14629
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14652 =
                               let uu____14653 =
                                 let uu____14680 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14680, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14653
                                in
                             mk uu____14652 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14715 ->
                           let uu____14716 =
                             let uu____14717 =
                               let uu____14718 =
                                 let uu____14745 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14745, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14718
                                in
                             mk uu____14717 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14716))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___186_14822 = cfg  in
                   {
                     steps =
                       (let uu___187_14825 = cfg.steps  in
                        {
                          beta = (uu___187_14825.beta);
                          iota = (uu___187_14825.iota);
                          zeta = (uu___187_14825.zeta);
                          weak = true;
                          hnf = (uu___187_14825.hnf);
                          primops = (uu___187_14825.primops);
                          do_not_unfold_pure_lets =
                            (uu___187_14825.do_not_unfold_pure_lets);
                          unfold_until = (uu___187_14825.unfold_until);
                          unfold_only = (uu___187_14825.unfold_only);
                          unfold_fully = (uu___187_14825.unfold_fully);
                          unfold_attr = (uu___187_14825.unfold_attr);
                          unfold_tac = (uu___187_14825.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___187_14825.pure_subterms_within_computations);
                          simplify = (uu___187_14825.simplify);
                          erase_universes = (uu___187_14825.erase_universes);
                          allow_unbound_universes =
                            (uu___187_14825.allow_unbound_universes);
                          reify_ = (uu___187_14825.reify_);
                          compress_uvars = (uu___187_14825.compress_uvars);
                          no_full_norm = (uu___187_14825.no_full_norm);
                          check_no_uvars = (uu___187_14825.check_no_uvars);
                          unmeta = (uu___187_14825.unmeta);
                          unascribe = (uu___187_14825.unascribe);
                          in_full_norm_request =
                            (uu___187_14825.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___187_14825.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___186_14822.tcenv);
                     debug = (uu___186_14822.debug);
                     delta_level = (uu___186_14822.delta_level);
                     primitive_steps = (uu___186_14822.primitive_steps);
                     strong = (uu___186_14822.strong);
                     memoize_lazy = (uu___186_14822.memoize_lazy);
                     normalize_pure_lets =
                       (uu___186_14822.normalize_pure_lets)
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
                         let uu____14861 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14861 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___188_14881 = cfg  in
                               let uu____14882 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___188_14881.steps);
                                 tcenv = uu____14882;
                                 debug = (uu___188_14881.debug);
                                 delta_level = (uu___188_14881.delta_level);
                                 primitive_steps =
                                   (uu___188_14881.primitive_steps);
                                 strong = (uu___188_14881.strong);
                                 memoize_lazy = (uu___188_14881.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_14881.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14889 =
                                 let uu____14890 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14890  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14889
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___189_14893 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___189_14893.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___189_14893.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___189_14893.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___189_14893.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14894 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14894
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14905,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14906;
                               FStar_Syntax_Syntax.lbunivs = uu____14907;
                               FStar_Syntax_Syntax.lbtyp = uu____14908;
                               FStar_Syntax_Syntax.lbeff = uu____14909;
                               FStar_Syntax_Syntax.lbdef = uu____14910;
                               FStar_Syntax_Syntax.lbattrs = uu____14911;
                               FStar_Syntax_Syntax.lbpos = uu____14912;_}::uu____14913),uu____14914)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14954 =
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
               if uu____14954
               then
                 let binder =
                   let uu____14956 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14956  in
                 let env1 =
                   let uu____14966 =
                     let uu____14973 =
                       let uu____14974 =
                         let uu____15005 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____15005,
                           false)
                          in
                       Clos uu____14974  in
                     ((FStar_Pervasives_Native.Some binder), uu____14973)  in
                   uu____14966 :: env  in
                 (log cfg
                    (fun uu____15100  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____15104  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____15105 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____15105))
                 else
                   (let uu____15107 =
                      let uu____15112 =
                        let uu____15113 =
                          let uu____15118 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____15118
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____15113]  in
                      FStar_Syntax_Subst.open_term uu____15112 body  in
                    match uu____15107 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____15139  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____15147 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____15147  in
                            FStar_Util.Inl
                              (let uu___190_15157 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___190_15157.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___190_15157.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____15160  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___191_15162 = lb  in
                             let uu____15163 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___191_15162.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___191_15162.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15163;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___191_15162.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___191_15162.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15188  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___192_15211 = cfg  in
                             {
                               steps = (uu___192_15211.steps);
                               tcenv = (uu___192_15211.tcenv);
                               debug = (uu___192_15211.debug);
                               delta_level = (uu___192_15211.delta_level);
                               primitive_steps =
                                 (uu___192_15211.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___192_15211.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___192_15211.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15214  ->
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
               let uu____15231 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15231 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15267 =
                               let uu___193_15268 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___193_15268.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___193_15268.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15267  in
                           let uu____15269 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15269 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15295 =
                                   FStar_List.map (fun uu____15311  -> dummy)
                                     lbs1
                                    in
                                 let uu____15312 =
                                   let uu____15321 =
                                     FStar_List.map
                                       (fun uu____15341  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15321 env  in
                                 FStar_List.append uu____15295 uu____15312
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15365 =
                                       let uu___194_15366 = rc  in
                                       let uu____15367 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___194_15366.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15367;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___194_15366.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15365
                                 | uu____15376 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___195_15382 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___195_15382.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___195_15382.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___195_15382.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___195_15382.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15392 =
                        FStar_List.map (fun uu____15408  -> dummy) lbs2  in
                      FStar_List.append uu____15392 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15416 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15416 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___196_15432 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___196_15432.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___196_15432.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15461 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15461
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15480 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15556  ->
                        match uu____15556 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___197_15677 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___197_15677.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___197_15677.FStar_Syntax_Syntax.sort)
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
               (match uu____15480 with
                | (rec_env,memos,uu____15904) ->
                    let uu____15957 =
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
                             let uu____16280 =
                               let uu____16287 =
                                 let uu____16288 =
                                   let uu____16319 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16319, false)
                                    in
                                 Clos uu____16288  in
                               (FStar_Pervasives_Native.None, uu____16287)
                                in
                             uu____16280 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16423  ->
                     let uu____16424 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16424);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16446 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16448::uu____16449 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16454) ->
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
                             | uu____16477 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16491 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16491
                              | uu____16502 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16508 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16534 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16550 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16565 =
                        let uu____16566 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16567 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16566 uu____16567
                         in
                      failwith uu____16565
                    else
                      (let uu____16569 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____16569)
                | uu____16570 -> norm cfg env stack t2))

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
                let uu____16580 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16580  in
              let uu____16581 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16581 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16594  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16605  ->
                        let uu____16606 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16607 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16606 uu____16607);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16612 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16612 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16621))::stack1 ->
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
                      | uu____16660 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16663 ->
                          let uu____16666 =
                            let uu____16667 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16667
                             in
                          failwith uu____16666
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
                  let uu___198_16691 = cfg  in
                  let uu____16692 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16692;
                    tcenv = (uu___198_16691.tcenv);
                    debug = (uu___198_16691.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___198_16691.primitive_steps);
                    strong = (uu___198_16691.strong);
                    memoize_lazy = (uu___198_16691.memoize_lazy);
                    normalize_pure_lets =
                      (uu___198_16691.normalize_pure_lets)
                  }
                else
                  (let uu___199_16694 = cfg  in
                   {
                     steps =
                       (let uu___200_16697 = cfg.steps  in
                        {
                          beta = (uu___200_16697.beta);
                          iota = (uu___200_16697.iota);
                          zeta = false;
                          weak = (uu___200_16697.weak);
                          hnf = (uu___200_16697.hnf);
                          primops = (uu___200_16697.primops);
                          do_not_unfold_pure_lets =
                            (uu___200_16697.do_not_unfold_pure_lets);
                          unfold_until = (uu___200_16697.unfold_until);
                          unfold_only = (uu___200_16697.unfold_only);
                          unfold_fully = (uu___200_16697.unfold_fully);
                          unfold_attr = (uu___200_16697.unfold_attr);
                          unfold_tac = (uu___200_16697.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___200_16697.pure_subterms_within_computations);
                          simplify = (uu___200_16697.simplify);
                          erase_universes = (uu___200_16697.erase_universes);
                          allow_unbound_universes =
                            (uu___200_16697.allow_unbound_universes);
                          reify_ = (uu___200_16697.reify_);
                          compress_uvars = (uu___200_16697.compress_uvars);
                          no_full_norm = (uu___200_16697.no_full_norm);
                          check_no_uvars = (uu___200_16697.check_no_uvars);
                          unmeta = (uu___200_16697.unmeta);
                          unascribe = (uu___200_16697.unascribe);
                          in_full_norm_request =
                            (uu___200_16697.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___200_16697.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___199_16694.tcenv);
                     debug = (uu___199_16694.debug);
                     delta_level = (uu___199_16694.delta_level);
                     primitive_steps = (uu___199_16694.primitive_steps);
                     strong = (uu___199_16694.strong);
                     memoize_lazy = (uu___199_16694.memoize_lazy);
                     normalize_pure_lets =
                       (uu___199_16694.normalize_pure_lets)
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
                  (fun uu____16731  ->
                     let uu____16732 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16733 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16732
                       uu____16733);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16735 =
                   let uu____16736 = FStar_Syntax_Subst.compress head3  in
                   uu____16736.FStar_Syntax_Syntax.n  in
                 match uu____16735 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16754 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16754
                        in
                     let uu____16755 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16755 with
                      | (uu____16756,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16766 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16776 =
                                   let uu____16777 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16777.FStar_Syntax_Syntax.n  in
                                 match uu____16776 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16783,uu____16784))
                                     ->
                                     let uu____16793 =
                                       let uu____16794 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16794.FStar_Syntax_Syntax.n  in
                                     (match uu____16793 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16800,msrc,uu____16802))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16811 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16811
                                      | uu____16812 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16813 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16814 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16814 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___201_16819 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___201_16819.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___201_16819.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___201_16819.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___201_16819.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___201_16819.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16820 = FStar_List.tl stack  in
                                    let uu____16821 =
                                      let uu____16822 =
                                        let uu____16829 =
                                          let uu____16830 =
                                            let uu____16843 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16843)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16830
                                           in
                                        FStar_Syntax_Syntax.mk uu____16829
                                         in
                                      uu____16822
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16820 uu____16821
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16859 =
                                      let uu____16860 = is_return body  in
                                      match uu____16860 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16864;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16865;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16868 -> false  in
                                    if uu____16859
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
                                         let uu____16889 =
                                           let uu____16896 =
                                             let uu____16897 =
                                               let uu____16914 =
                                                 let uu____16921 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16921]  in
                                               (uu____16914, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16897
                                              in
                                           FStar_Syntax_Syntax.mk uu____16896
                                            in
                                         uu____16889
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16955 =
                                           let uu____16956 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16956.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16955 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16962::uu____16963::[])
                                             ->
                                             let uu____16968 =
                                               let uu____16975 =
                                                 let uu____16976 =
                                                   let uu____16983 =
                                                     let uu____16984 =
                                                       let uu____16985 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16985
                                                        in
                                                     let uu____16986 =
                                                       let uu____16989 =
                                                         let uu____16990 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16990
                                                          in
                                                       [uu____16989]  in
                                                     uu____16984 ::
                                                       uu____16986
                                                      in
                                                   (bind1, uu____16983)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16976
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16975
                                                in
                                             uu____16968
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16996 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____17008 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____17008
                                         then
                                           let uu____17017 =
                                             let uu____17024 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17024
                                              in
                                           let uu____17025 =
                                             let uu____17034 =
                                               let uu____17041 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____17041
                                                in
                                             [uu____17034]  in
                                           uu____17017 :: uu____17025
                                         else []  in
                                       let reified =
                                         let uu____17070 =
                                           let uu____17077 =
                                             let uu____17078 =
                                               let uu____17093 =
                                                 let uu____17102 =
                                                   let uu____17111 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____17118 =
                                                     let uu____17127 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____17127]  in
                                                   uu____17111 :: uu____17118
                                                    in
                                                 let uu____17152 =
                                                   let uu____17161 =
                                                     let uu____17170 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____17177 =
                                                       let uu____17186 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____17193 =
                                                         let uu____17202 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____17209 =
                                                           let uu____17218 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____17218]  in
                                                         uu____17202 ::
                                                           uu____17209
                                                          in
                                                       uu____17186 ::
                                                         uu____17193
                                                        in
                                                     uu____17170 ::
                                                       uu____17177
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____17161
                                                    in
                                                 FStar_List.append
                                                   uu____17102 uu____17152
                                                  in
                                               (bind_inst, uu____17093)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____17078
                                              in
                                           FStar_Syntax_Syntax.mk uu____17077
                                            in
                                         uu____17070
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____17284  ->
                                            let uu____17285 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____17286 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____17285 uu____17286);
                                       (let uu____17287 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____17287 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____17311 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____17311
                        in
                     let uu____17312 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17312 with
                      | (uu____17313,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17350 =
                                  let uu____17351 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____17351.FStar_Syntax_Syntax.n  in
                                match uu____17350 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17355) -> t2
                                | uu____17360 -> head4  in
                              let uu____17361 =
                                let uu____17362 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17362.FStar_Syntax_Syntax.n  in
                              match uu____17361 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17368 -> FStar_Pervasives_Native.None
                               in
                            let uu____17369 = maybe_extract_fv head4  in
                            match uu____17369 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17379 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17379
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17384 = maybe_extract_fv head5
                                     in
                                  match uu____17384 with
                                  | FStar_Pervasives_Native.Some uu____17389
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17390 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17395 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17410 =
                              match uu____17410 with
                              | (e,q) ->
                                  let uu____17417 =
                                    let uu____17418 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17418.FStar_Syntax_Syntax.n  in
                                  (match uu____17417 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17433 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17433
                                   | uu____17434 -> false)
                               in
                            let uu____17435 =
                              let uu____17436 =
                                let uu____17445 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17445 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17436
                               in
                            if uu____17435
                            then
                              let uu____17464 =
                                let uu____17465 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17465
                                 in
                              failwith uu____17464
                            else ());
                           (let uu____17467 = maybe_unfold_action head_app
                               in
                            match uu____17467 with
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
                                   (fun uu____17510  ->
                                      let uu____17511 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17512 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17511 uu____17512);
                                 (let uu____17513 = FStar_List.tl stack  in
                                  norm cfg env uu____17513 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17515) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17539 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17539  in
                     (log cfg
                        (fun uu____17543  ->
                           let uu____17544 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17544);
                      (let uu____17545 = FStar_List.tl stack  in
                       norm cfg env uu____17545 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17666  ->
                               match uu____17666 with
                               | (pat,wopt,tm) ->
                                   let uu____17714 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17714)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17746 = FStar_List.tl stack  in
                     norm cfg env uu____17746 tm
                 | uu____17747 -> fallback ())

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
              (fun uu____17761  ->
                 let uu____17762 = FStar_Ident.string_of_lid msrc  in
                 let uu____17763 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17764 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17762
                   uu____17763 uu____17764);
            (let uu____17765 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17765
             then
               let ed =
                 let uu____17767 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17767  in
               let uu____17768 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17768 with
               | (uu____17769,return_repr) ->
                   let return_inst =
                     let uu____17782 =
                       let uu____17783 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17783.FStar_Syntax_Syntax.n  in
                     match uu____17782 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17789::[]) ->
                         let uu____17794 =
                           let uu____17801 =
                             let uu____17802 =
                               let uu____17809 =
                                 let uu____17810 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17810]  in
                               (return_tm, uu____17809)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17802  in
                           FStar_Syntax_Syntax.mk uu____17801  in
                         uu____17794 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17816 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17819 =
                     let uu____17826 =
                       let uu____17827 =
                         let uu____17842 =
                           let uu____17851 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17858 =
                             let uu____17867 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17867]  in
                           uu____17851 :: uu____17858  in
                         (return_inst, uu____17842)  in
                       FStar_Syntax_Syntax.Tm_app uu____17827  in
                     FStar_Syntax_Syntax.mk uu____17826  in
                   uu____17819 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17906 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17906 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17909 =
                      let uu____17910 = FStar_Ident.text_of_lid msrc  in
                      let uu____17911 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17910 uu____17911
                       in
                    failwith uu____17909
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17912;
                      FStar_TypeChecker_Env.mtarget = uu____17913;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17914;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17936 =
                      let uu____17937 = FStar_Ident.text_of_lid msrc  in
                      let uu____17938 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17937 uu____17938
                       in
                    failwith uu____17936
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17939;
                      FStar_TypeChecker_Env.mtarget = uu____17940;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17941;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17976 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17977 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17976 t FStar_Syntax_Syntax.tun uu____17977))

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
                (fun uu____18033  ->
                   match uu____18033 with
                   | (a,imp) ->
                       let uu____18044 = norm cfg env [] a  in
                       (uu____18044, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____18052  ->
             let uu____18053 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____18054 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____18053 uu____18054);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____18078 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____18078
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___202_18081 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___202_18081.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___202_18081.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____18103 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____18103
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___203_18106 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___203_18106.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___203_18106.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____18143  ->
                      match uu____18143 with
                      | (a,i) ->
                          let uu____18154 = norm cfg env [] a  in
                          (uu____18154, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___116_18172  ->
                       match uu___116_18172 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____18176 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____18176
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___204_18184 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___205_18187 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___205_18187.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___204_18184.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___204_18184.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____18190  ->
        match uu____18190 with
        | (x,imp) ->
            let uu____18193 =
              let uu___206_18194 = x  in
              let uu____18195 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___206_18194.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___206_18194.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18195
              }  in
            (uu____18193, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18201 =
          FStar_List.fold_left
            (fun uu____18235  ->
               fun b  ->
                 match uu____18235 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18201 with | (nbs,uu____18315) -> FStar_List.rev nbs

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
            let uu____18347 =
              let uu___207_18348 = rc  in
              let uu____18349 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___207_18348.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18349;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___207_18348.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18347
        | uu____18358 -> lopt

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
            (let uu____18379 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18380 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____18379
               uu____18380)
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
          let uu____18402 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18402
          then tm1
          else
            (let w t =
               let uu___208_18416 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___208_18416.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___208_18416.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18427 =
                 let uu____18428 = FStar_Syntax_Util.unmeta t  in
                 uu____18428.FStar_Syntax_Syntax.n  in
               match uu____18427 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18435 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18484)::args1,(bv,uu____18487)::bs1) ->
                   let uu____18521 =
                     let uu____18522 = FStar_Syntax_Subst.compress t  in
                     uu____18522.FStar_Syntax_Syntax.n  in
                   (match uu____18521 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18526 -> false)
               | ([],[]) -> true
               | (uu____18547,uu____18548) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18589 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18590 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18589
                    uu____18590)
               else ();
               (let uu____18592 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18592 with
                | (hd1,args) ->
                    let uu____18625 =
                      let uu____18626 = FStar_Syntax_Subst.compress hd1  in
                      uu____18626.FStar_Syntax_Syntax.n  in
                    (match uu____18625 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____18633 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18634 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18635 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18633 uu____18634 uu____18635)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18637 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18654 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18655 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18654
                    uu____18655)
               else ();
               (let uu____18657 = FStar_Syntax_Util.is_squash t  in
                match uu____18657 with
                | FStar_Pervasives_Native.Some (uu____18668,t') ->
                    is_applied bs t'
                | uu____18680 ->
                    let uu____18689 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18689 with
                     | FStar_Pervasives_Native.Some (uu____18700,t') ->
                         is_applied bs t'
                     | uu____18712 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18736 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18736 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18743)::(q,uu____18745)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18773 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18774 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18773 uu____18774)
                    else ();
                    (let uu____18776 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18776 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18781 =
                           let uu____18782 = FStar_Syntax_Subst.compress p
                              in
                           uu____18782.FStar_Syntax_Syntax.n  in
                         (match uu____18781 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18790 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18790))
                          | uu____18793 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18796)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18813 =
                           let uu____18814 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18814.FStar_Syntax_Syntax.n  in
                         (match uu____18813 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18822 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18822))
                          | uu____18825 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18829 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18829 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18834 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18834 with
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
                                     let uu____18845 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18845))
                               | uu____18848 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18853)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18870 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18870 with
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
                                     let uu____18881 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18881))
                               | uu____18884 -> FStar_Pervasives_Native.None)
                          | uu____18887 -> FStar_Pervasives_Native.None)
                     | uu____18890 -> FStar_Pervasives_Native.None))
               | uu____18893 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18906 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18906 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18912)::[],uu____18913,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18924 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18925 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18924
                         uu____18925)
                    else ();
                    is_quantified_const bv phi')
               | uu____18927 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18940 =
                 let uu____18941 = FStar_Syntax_Subst.compress phi  in
                 uu____18941.FStar_Syntax_Syntax.n  in
               match uu____18940 with
               | FStar_Syntax_Syntax.Tm_match (uu____18946,br::brs) ->
                   let uu____19013 = br  in
                   (match uu____19013 with
                    | (uu____19030,uu____19031,e) ->
                        let r =
                          let uu____19052 = simp_t e  in
                          match uu____19052 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____19058 =
                                FStar_List.for_all
                                  (fun uu____19076  ->
                                     match uu____19076 with
                                     | (uu____19089,uu____19090,e') ->
                                         let uu____19104 = simp_t e'  in
                                         uu____19104 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____19058
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____19112 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____19121 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____19121
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____19152 =
                 match uu____19152 with
                 | (t1,q) ->
                     let uu____19165 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____19165 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19193 -> (t1, q))
                  in
               let uu____19204 = FStar_Syntax_Util.head_and_args t  in
               match uu____19204 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19270 =
                 let uu____19271 = FStar_Syntax_Util.unmeta ty  in
                 uu____19271.FStar_Syntax_Syntax.n  in
               match uu____19270 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19275) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19280,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19300 -> false  in
             let simplify1 arg =
               let uu____19325 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19325, arg)  in
             let uu____19334 = is_forall_const tm1  in
             match uu____19334 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____19339 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19340 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19339
                       uu____19340)
                  else ();
                  (let uu____19342 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19342))
             | FStar_Pervasives_Native.None  ->
                 let uu____19343 =
                   let uu____19344 = FStar_Syntax_Subst.compress tm1  in
                   uu____19344.FStar_Syntax_Syntax.n  in
                 (match uu____19343 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19348;
                              FStar_Syntax_Syntax.vars = uu____19349;_},uu____19350);
                         FStar_Syntax_Syntax.pos = uu____19351;
                         FStar_Syntax_Syntax.vars = uu____19352;_},args)
                      ->
                      let uu____19378 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19378
                      then
                        let uu____19379 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19379 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19424)::
                             (uu____19425,(arg,uu____19427))::[] ->
                             maybe_auto_squash arg
                         | (uu____19476,(arg,uu____19478))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19479)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19528)::uu____19529::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19580::(FStar_Pervasives_Native.Some (false
                                         ),uu____19581)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19632 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19646 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19646
                         then
                           let uu____19647 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19647 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19692)::uu____19693::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19744::(FStar_Pervasives_Native.Some (true
                                           ),uu____19745)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19796)::(uu____19797,(arg,uu____19799))::[]
                               -> maybe_auto_squash arg
                           | (uu____19848,(arg,uu____19850))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19851)::[]
                               -> maybe_auto_squash arg
                           | uu____19900 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19914 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19914
                            then
                              let uu____19915 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19915 with
                              | uu____19960::(FStar_Pervasives_Native.Some
                                              (true ),uu____19961)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20012)::uu____20013::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20064)::(uu____20065,(arg,uu____20067))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20116,(p,uu____20118))::(uu____20119,
                                                                (q,uu____20121))::[]
                                  ->
                                  let uu____20168 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20168
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20170 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20184 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20184
                               then
                                 let uu____20185 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20185 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20230)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20231)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20282)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20283)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20334)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20335)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20386)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20387)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20438,(arg,uu____20440))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20441)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20490)::(uu____20491,(arg,uu____20493))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20542,(arg,uu____20544))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20545)::[]
                                     ->
                                     let uu____20594 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20594
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20595)::(uu____20596,(arg,uu____20598))::[]
                                     ->
                                     let uu____20647 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20647
                                 | (uu____20648,(p,uu____20650))::(uu____20651,
                                                                   (q,uu____20653))::[]
                                     ->
                                     let uu____20700 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20700
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20702 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20716 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20716
                                  then
                                    let uu____20717 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20717 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20762)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20793)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20824 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20838 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20838
                                     then
                                       match args with
                                       | (t,uu____20840)::[] ->
                                           let uu____20857 =
                                             let uu____20858 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20858.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20857 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20861::[],body,uu____20863)
                                                ->
                                                let uu____20890 = simp_t body
                                                   in
                                                (match uu____20890 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20893 -> tm1)
                                            | uu____20896 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20898))::(t,uu____20900)::[]
                                           ->
                                           let uu____20927 =
                                             let uu____20928 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20928.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20927 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20931::[],body,uu____20933)
                                                ->
                                                let uu____20960 = simp_t body
                                                   in
                                                (match uu____20960 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20963 -> tm1)
                                            | uu____20966 -> tm1)
                                       | uu____20967 -> tm1
                                     else
                                       (let uu____20977 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20977
                                        then
                                          match args with
                                          | (t,uu____20979)::[] ->
                                              let uu____20996 =
                                                let uu____20997 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20997.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20996 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21000::[],body,uu____21002)
                                                   ->
                                                   let uu____21029 =
                                                     simp_t body  in
                                                   (match uu____21029 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21032 -> tm1)
                                               | uu____21035 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21037))::(t,uu____21039)::[]
                                              ->
                                              let uu____21066 =
                                                let uu____21067 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21067.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21066 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21070::[],body,uu____21072)
                                                   ->
                                                   let uu____21099 =
                                                     simp_t body  in
                                                   (match uu____21099 with
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
                                                    | uu____21102 -> tm1)
                                               | uu____21105 -> tm1)
                                          | uu____21106 -> tm1
                                        else
                                          (let uu____21116 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21116
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21117;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21118;_},uu____21119)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21136;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21137;_},uu____21138)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21155 -> tm1
                                           else
                                             (let uu____21165 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____21165 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____21185 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21195;
                         FStar_Syntax_Syntax.vars = uu____21196;_},args)
                      ->
                      let uu____21218 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21218
                      then
                        let uu____21219 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21219 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21264)::
                             (uu____21265,(arg,uu____21267))::[] ->
                             maybe_auto_squash arg
                         | (uu____21316,(arg,uu____21318))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21319)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21368)::uu____21369::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21420::(FStar_Pervasives_Native.Some (false
                                         ),uu____21421)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21472 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21486 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21486
                         then
                           let uu____21487 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21487 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21532)::uu____21533::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21584::(FStar_Pervasives_Native.Some (true
                                           ),uu____21585)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21636)::(uu____21637,(arg,uu____21639))::[]
                               -> maybe_auto_squash arg
                           | (uu____21688,(arg,uu____21690))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21691)::[]
                               -> maybe_auto_squash arg
                           | uu____21740 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21754 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21754
                            then
                              let uu____21755 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21755 with
                              | uu____21800::(FStar_Pervasives_Native.Some
                                              (true ),uu____21801)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21852)::uu____21853::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21904)::(uu____21905,(arg,uu____21907))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21956,(p,uu____21958))::(uu____21959,
                                                                (q,uu____21961))::[]
                                  ->
                                  let uu____22008 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22008
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22010 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22024 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22024
                               then
                                 let uu____22025 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22025 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22070)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22071)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22122)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22123)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22174)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22175)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22226)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22227)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22278,(arg,uu____22280))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22281)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22330)::(uu____22331,(arg,uu____22333))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22382,(arg,uu____22384))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22385)::[]
                                     ->
                                     let uu____22434 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22434
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22435)::(uu____22436,(arg,uu____22438))::[]
                                     ->
                                     let uu____22487 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22487
                                 | (uu____22488,(p,uu____22490))::(uu____22491,
                                                                   (q,uu____22493))::[]
                                     ->
                                     let uu____22540 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22540
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22542 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22556 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22556
                                  then
                                    let uu____22557 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22557 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22602)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22633)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22664 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22678 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22678
                                     then
                                       match args with
                                       | (t,uu____22680)::[] ->
                                           let uu____22697 =
                                             let uu____22698 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22698.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22697 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22701::[],body,uu____22703)
                                                ->
                                                let uu____22730 = simp_t body
                                                   in
                                                (match uu____22730 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22733 -> tm1)
                                            | uu____22736 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22738))::(t,uu____22740)::[]
                                           ->
                                           let uu____22767 =
                                             let uu____22768 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22768.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22767 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22771::[],body,uu____22773)
                                                ->
                                                let uu____22800 = simp_t body
                                                   in
                                                (match uu____22800 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22803 -> tm1)
                                            | uu____22806 -> tm1)
                                       | uu____22807 -> tm1
                                     else
                                       (let uu____22817 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22817
                                        then
                                          match args with
                                          | (t,uu____22819)::[] ->
                                              let uu____22836 =
                                                let uu____22837 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22837.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22836 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22840::[],body,uu____22842)
                                                   ->
                                                   let uu____22869 =
                                                     simp_t body  in
                                                   (match uu____22869 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22872 -> tm1)
                                               | uu____22875 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22877))::(t,uu____22879)::[]
                                              ->
                                              let uu____22906 =
                                                let uu____22907 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22907.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22906 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22910::[],body,uu____22912)
                                                   ->
                                                   let uu____22939 =
                                                     simp_t body  in
                                                   (match uu____22939 with
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
                                                    | uu____22942 -> tm1)
                                               | uu____22945 -> tm1)
                                          | uu____22946 -> tm1
                                        else
                                          (let uu____22956 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22956
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22957;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22958;_},uu____22959)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22976;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22977;_},uu____22978)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22995 -> tm1
                                           else
                                             (let uu____23005 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____23005 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____23025 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23040 = simp_t t  in
                      (match uu____23040 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____23043 ->
                      let uu____23066 = is_const_match tm1  in
                      (match uu____23066 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____23069 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____23079  ->
               (let uu____23081 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23082 = FStar_Syntax_Print.term_to_string t  in
                let uu____23083 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23090 =
                  let uu____23091 =
                    let uu____23094 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23094
                     in
                  stack_to_string uu____23091  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23081 uu____23082 uu____23083 uu____23090);
               (let uu____23117 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23117
                then
                  let uu____23118 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23118 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23125 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23126 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23127 =
                          let uu____23128 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23128
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23125
                          uu____23126 uu____23127);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____23146 =
                     let uu____23147 =
                       let uu____23148 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____23148  in
                     FStar_Util.string_of_int uu____23147  in
                   let uu____23153 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____23154 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____23146 uu____23153 uu____23154)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____23160,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____23211  ->
                     let uu____23212 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____23212);
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
               let uu____23250 =
                 let uu___209_23251 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___209_23251.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___209_23251.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____23250
           | (Arg (Univ uu____23254,uu____23255,uu____23256))::uu____23257 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____23260,uu____23261))::uu____23262 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____23277,uu____23278),aq,r))::stack1
               when
               let uu____23328 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23328 ->
               let t2 =
                 let uu____23332 =
                   let uu____23337 =
                     let uu____23338 = closure_as_term cfg env_arg tm  in
                     (uu____23338, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____23337  in
                 uu____23332 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____23348),aq,r))::stack1 ->
               (log cfg
                  (fun uu____23401  ->
                     let uu____23402 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____23402);
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
                  (let uu____23414 = FStar_ST.op_Bang m  in
                   match uu____23414 with
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
                   | FStar_Pervasives_Native.Some (uu____23557,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23610 =
                 log cfg
                   (fun uu____23614  ->
                      let uu____23615 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23615);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23621 =
                 let uu____23622 = FStar_Syntax_Subst.compress t1  in
                 uu____23622.FStar_Syntax_Syntax.n  in
               (match uu____23621 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23649 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23649  in
                    (log cfg
                       (fun uu____23653  ->
                          let uu____23654 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23654);
                     (let uu____23655 = FStar_List.tl stack  in
                      norm cfg env1 uu____23655 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23656);
                       FStar_Syntax_Syntax.pos = uu____23657;
                       FStar_Syntax_Syntax.vars = uu____23658;_},(e,uu____23660)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23689 when
                    (cfg.steps).primops ->
                    let uu____23704 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23704 with
                     | (hd1,args) ->
                         let uu____23741 =
                           let uu____23742 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23742.FStar_Syntax_Syntax.n  in
                         (match uu____23741 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23746 = find_prim_step cfg fv  in
                              (match uu____23746 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23749; arity = uu____23750;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23752;
                                     requires_binder_substitution =
                                       uu____23753;
                                     interpretation = uu____23754;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23769 -> fallback " (3)" ())
                          | uu____23772 -> fallback " (4)" ()))
                | uu____23773 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23796  ->
                     let uu____23797 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23797);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23806 =
                   log cfg1
                     (fun uu____23811  ->
                        let uu____23812 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23813 =
                          let uu____23814 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23841  ->
                                    match uu____23841 with
                                    | (p,uu____23851,uu____23852) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23814
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23812 uu____23813);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___117_23869  ->
                                match uu___117_23869 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23870 -> false))
                         in
                      let steps =
                        let uu___210_23872 = cfg1.steps  in
                        {
                          beta = (uu___210_23872.beta);
                          iota = (uu___210_23872.iota);
                          zeta = false;
                          weak = (uu___210_23872.weak);
                          hnf = (uu___210_23872.hnf);
                          primops = (uu___210_23872.primops);
                          do_not_unfold_pure_lets =
                            (uu___210_23872.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___210_23872.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___210_23872.pure_subterms_within_computations);
                          simplify = (uu___210_23872.simplify);
                          erase_universes = (uu___210_23872.erase_universes);
                          allow_unbound_universes =
                            (uu___210_23872.allow_unbound_universes);
                          reify_ = (uu___210_23872.reify_);
                          compress_uvars = (uu___210_23872.compress_uvars);
                          no_full_norm = (uu___210_23872.no_full_norm);
                          check_no_uvars = (uu___210_23872.check_no_uvars);
                          unmeta = (uu___210_23872.unmeta);
                          unascribe = (uu___210_23872.unascribe);
                          in_full_norm_request =
                            (uu___210_23872.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___210_23872.weakly_reduce_scrutinee)
                        }  in
                      let uu___211_23877 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___211_23877.tcenv);
                        debug = (uu___211_23877.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___211_23877.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___211_23877.memoize_lazy);
                        normalize_pure_lets =
                          (uu___211_23877.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23949 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23978 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____24062  ->
                                    fun uu____24063  ->
                                      match (uu____24062, uu____24063) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____24202 = norm_pat env3 p1
                                             in
                                          (match uu____24202 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23978 with
                           | (pats1,env3) ->
                               ((let uu___212_24364 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___212_24364.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___213_24383 = x  in
                            let uu____24384 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___213_24383.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___213_24383.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24384
                            }  in
                          ((let uu___214_24398 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___214_24398.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___215_24409 = x  in
                            let uu____24410 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___215_24409.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___215_24409.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24410
                            }  in
                          ((let uu___216_24424 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___216_24424.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___217_24440 = x  in
                            let uu____24441 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___217_24440.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___217_24440.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24441
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___218_24456 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___218_24456.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24500 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24530 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24530 with
                                  | (p,wopt,e) ->
                                      let uu____24550 = norm_pat env1 p  in
                                      (match uu____24550 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24605 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24605
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24622 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24622
                      then
                        norm
                          (let uu___219_24627 = cfg1  in
                           {
                             steps =
                               (let uu___220_24630 = cfg1.steps  in
                                {
                                  beta = (uu___220_24630.beta);
                                  iota = (uu___220_24630.iota);
                                  zeta = (uu___220_24630.zeta);
                                  weak = (uu___220_24630.weak);
                                  hnf = (uu___220_24630.hnf);
                                  primops = (uu___220_24630.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___220_24630.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___220_24630.unfold_until);
                                  unfold_only = (uu___220_24630.unfold_only);
                                  unfold_fully =
                                    (uu___220_24630.unfold_fully);
                                  unfold_attr = (uu___220_24630.unfold_attr);
                                  unfold_tac = (uu___220_24630.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___220_24630.pure_subterms_within_computations);
                                  simplify = (uu___220_24630.simplify);
                                  erase_universes =
                                    (uu___220_24630.erase_universes);
                                  allow_unbound_universes =
                                    (uu___220_24630.allow_unbound_universes);
                                  reify_ = (uu___220_24630.reify_);
                                  compress_uvars =
                                    (uu___220_24630.compress_uvars);
                                  no_full_norm =
                                    (uu___220_24630.no_full_norm);
                                  check_no_uvars =
                                    (uu___220_24630.check_no_uvars);
                                  unmeta = (uu___220_24630.unmeta);
                                  unascribe = (uu___220_24630.unascribe);
                                  in_full_norm_request =
                                    (uu___220_24630.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___219_24627.tcenv);
                             debug = (uu___219_24627.debug);
                             delta_level = (uu___219_24627.delta_level);
                             primitive_steps =
                               (uu___219_24627.primitive_steps);
                             strong = (uu___219_24627.strong);
                             memoize_lazy = (uu___219_24627.memoize_lazy);
                             normalize_pure_lets =
                               (uu___219_24627.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24632 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24632)
                    in
                 let rec is_cons head1 =
                   let uu____24657 =
                     let uu____24658 = FStar_Syntax_Subst.compress head1  in
                     uu____24658.FStar_Syntax_Syntax.n  in
                   match uu____24657 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24662) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24667 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24668;
                         FStar_Syntax_Syntax.fv_delta = uu____24669;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24670;
                         FStar_Syntax_Syntax.fv_delta = uu____24671;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24672);_}
                       -> true
                   | uu____24679 -> false  in
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
                   let uu____24842 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24842 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24929 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24968 ->
                                 let uu____24969 =
                                   let uu____24970 = is_cons head1  in
                                   Prims.op_Negation uu____24970  in
                                 FStar_Util.Inr uu____24969)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24995 =
                              let uu____24996 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24996.FStar_Syntax_Syntax.n  in
                            (match uu____24995 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____25014 ->
                                 let uu____25015 =
                                   let uu____25016 = is_cons head1  in
                                   Prims.op_Negation uu____25016  in
                                 FStar_Util.Inr uu____25015))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____25093)::rest_a,(p1,uu____25096)::rest_p) ->
                       let uu____25140 = matches_pat t2 p1  in
                       (match uu____25140 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____25189 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____25307 = matches_pat scrutinee1 p1  in
                       (match uu____25307 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____25347  ->
                                  let uu____25348 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____25349 =
                                    let uu____25350 =
                                      FStar_List.map
                                        (fun uu____25360  ->
                                           match uu____25360 with
                                           | (uu____25365,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____25350
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____25348 uu____25349);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____25397  ->
                                       match uu____25397 with
                                       | (bv,t2) ->
                                           let uu____25420 =
                                             let uu____25427 =
                                               let uu____25430 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____25430
                                                in
                                             let uu____25431 =
                                               let uu____25432 =
                                                 let uu____25463 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____25463, false)
                                                  in
                                               Clos uu____25432  in
                                             (uu____25427, uu____25431)  in
                                           uu____25420 :: env2) env1 s
                                 in
                              let uu____25576 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25576)))
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
    let uu____25603 =
      let uu____25606 = FStar_ST.op_Bang plugins  in p :: uu____25606  in
    FStar_ST.op_Colon_Equals plugins uu____25603  in
  let retrieve uu____25714 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25791  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___118_25832  ->
                  match uu___118_25832 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25836 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25842 -> d  in
        let uu____25845 = to_fsteps s  in
        let uu____25846 =
          let uu____25847 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25848 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25849 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25850 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____25851 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25852 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25847;
            primop = uu____25848;
            b380 = uu____25849;
            wpe = uu____25850;
            norm_delayed = uu____25851;
            print_normalized = uu____25852
          }  in
        let uu____25853 =
          let uu____25856 =
            let uu____25859 = retrieve_plugins ()  in
            FStar_List.append uu____25859 psteps  in
          add_steps built_in_primitive_steps uu____25856  in
        let uu____25862 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25864 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25864)
           in
        {
          steps = uu____25845;
          tcenv = e;
          debug = uu____25846;
          delta_level = d1;
          primitive_steps = uu____25853;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25862
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
      fun t  -> let uu____25946 = config s e  in norm_comp uu____25946 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25963 = config [] env  in norm_universe uu____25963 [] u
  
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
        let uu____25987 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25987  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25994 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___221_26013 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___221_26013.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___221_26013.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____26020 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26020
          then
            let ct1 =
              let uu____26022 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26022 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____26029 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26029
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___222_26033 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___222_26033.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___222_26033.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___222_26033.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___223_26035 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___223_26035.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___223_26035.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___223_26035.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___223_26035.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___224_26036 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___224_26036.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___224_26036.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26038 -> c
  
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
        let uu____26056 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____26056  in
      let uu____26063 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____26063
      then
        let uu____26064 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____26064 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____26070  ->
                 let uu____26071 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____26071)
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
            ((let uu____26092 =
                let uu____26097 =
                  let uu____26098 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26098
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26097)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26092);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____26113 = config [AllowUnboundUniverses] env  in
          norm_comp uu____26113 [] c
        with
        | e ->
            ((let uu____26126 =
                let uu____26131 =
                  let uu____26132 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26132
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26131)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26126);
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
                   let uu____26177 =
                     let uu____26178 =
                       let uu____26185 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26185)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26178  in
                   mk uu____26177 t01.FStar_Syntax_Syntax.pos
               | uu____26190 -> t2)
          | uu____26191 -> t2  in
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
        let uu____26255 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26255 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26284 ->
                 let uu____26291 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26291 with
                  | (actuals,uu____26301,uu____26302) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26316 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26316 with
                         | (binders,args) ->
                             let uu____26327 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26327
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
      | uu____26341 ->
          let uu____26342 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26342 with
           | (head1,args) ->
               let uu____26379 =
                 let uu____26380 = FStar_Syntax_Subst.compress head1  in
                 uu____26380.FStar_Syntax_Syntax.n  in
               (match uu____26379 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26405 =
                      let uu____26418 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26418  in
                    (match uu____26405 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26448 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___229_26456 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___229_26456.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___229_26456.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___229_26456.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___229_26456.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___229_26456.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___229_26456.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___229_26456.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___229_26456.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___229_26456.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___229_26456.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___229_26456.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___229_26456.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___229_26456.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___229_26456.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___229_26456.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___229_26456.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___229_26456.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___229_26456.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___229_26456.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___229_26456.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___229_26456.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___229_26456.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___229_26456.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___229_26456.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___229_26456.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___229_26456.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___229_26456.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___229_26456.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___229_26456.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___229_26456.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___229_26456.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___229_26456.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___229_26456.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___229_26456.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___229_26456.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___229_26456.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____26448 with
                            | (uu____26457,ty,uu____26459) ->
                                eta_expand_with_type env t ty))
                | uu____26460 ->
                    let uu____26461 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___230_26469 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___230_26469.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___230_26469.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___230_26469.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___230_26469.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___230_26469.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___230_26469.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___230_26469.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___230_26469.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___230_26469.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___230_26469.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___230_26469.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___230_26469.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___230_26469.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___230_26469.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___230_26469.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___230_26469.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___230_26469.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___230_26469.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___230_26469.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___230_26469.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___230_26469.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___230_26469.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___230_26469.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___230_26469.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___230_26469.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___230_26469.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___230_26469.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___230_26469.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___230_26469.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___230_26469.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___230_26469.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___230_26469.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___230_26469.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___230_26469.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___230_26469.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___230_26469.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____26461 with
                     | (uu____26470,ty,uu____26472) ->
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
      let uu___231_26545 = x  in
      let uu____26546 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___231_26545.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___231_26545.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26546
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26549 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26574 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26575 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26576 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26577 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26584 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26585 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26586 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___232_26616 = rc  in
          let uu____26617 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26626 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___232_26616.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26617;
            FStar_Syntax_Syntax.residual_flags = uu____26626
          }  in
        let uu____26629 =
          let uu____26630 =
            let uu____26647 = elim_delayed_subst_binders bs  in
            let uu____26654 = elim_delayed_subst_term t2  in
            let uu____26657 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26647, uu____26654, uu____26657)  in
          FStar_Syntax_Syntax.Tm_abs uu____26630  in
        mk1 uu____26629
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26688 =
          let uu____26689 =
            let uu____26702 = elim_delayed_subst_binders bs  in
            let uu____26709 = elim_delayed_subst_comp c  in
            (uu____26702, uu____26709)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26689  in
        mk1 uu____26688
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26726 =
          let uu____26727 =
            let uu____26734 = elim_bv bv  in
            let uu____26735 = elim_delayed_subst_term phi  in
            (uu____26734, uu____26735)  in
          FStar_Syntax_Syntax.Tm_refine uu____26727  in
        mk1 uu____26726
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26762 =
          let uu____26763 =
            let uu____26778 = elim_delayed_subst_term t2  in
            let uu____26781 = elim_delayed_subst_args args  in
            (uu____26778, uu____26781)  in
          FStar_Syntax_Syntax.Tm_app uu____26763  in
        mk1 uu____26762
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___233_26849 = p  in
              let uu____26850 =
                let uu____26851 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26851  in
              {
                FStar_Syntax_Syntax.v = uu____26850;
                FStar_Syntax_Syntax.p =
                  (uu___233_26849.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___234_26853 = p  in
              let uu____26854 =
                let uu____26855 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26855  in
              {
                FStar_Syntax_Syntax.v = uu____26854;
                FStar_Syntax_Syntax.p =
                  (uu___234_26853.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___235_26862 = p  in
              let uu____26863 =
                let uu____26864 =
                  let uu____26871 = elim_bv x  in
                  let uu____26872 = elim_delayed_subst_term t0  in
                  (uu____26871, uu____26872)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26864  in
              {
                FStar_Syntax_Syntax.v = uu____26863;
                FStar_Syntax_Syntax.p =
                  (uu___235_26862.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___236_26895 = p  in
              let uu____26896 =
                let uu____26897 =
                  let uu____26910 =
                    FStar_List.map
                      (fun uu____26933  ->
                         match uu____26933 with
                         | (x,b) ->
                             let uu____26946 = elim_pat x  in
                             (uu____26946, b)) pats
                     in
                  (fv, uu____26910)  in
                FStar_Syntax_Syntax.Pat_cons uu____26897  in
              {
                FStar_Syntax_Syntax.v = uu____26896;
                FStar_Syntax_Syntax.p =
                  (uu___236_26895.FStar_Syntax_Syntax.p)
              }
          | uu____26959 -> p  in
        let elim_branch uu____26983 =
          match uu____26983 with
          | (pat,wopt,t3) ->
              let uu____27009 = elim_pat pat  in
              let uu____27012 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27015 = elim_delayed_subst_term t3  in
              (uu____27009, uu____27012, uu____27015)
           in
        let uu____27020 =
          let uu____27021 =
            let uu____27044 = elim_delayed_subst_term t2  in
            let uu____27047 = FStar_List.map elim_branch branches  in
            (uu____27044, uu____27047)  in
          FStar_Syntax_Syntax.Tm_match uu____27021  in
        mk1 uu____27020
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____27178 =
          match uu____27178 with
          | (tc,topt) ->
              let uu____27213 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27223 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27223
                | FStar_Util.Inr c ->
                    let uu____27225 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27225
                 in
              let uu____27226 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27213, uu____27226)
           in
        let uu____27235 =
          let uu____27236 =
            let uu____27263 = elim_delayed_subst_term t2  in
            let uu____27266 = elim_ascription a  in
            (uu____27263, uu____27266, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27236  in
        mk1 uu____27235
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___237_27327 = lb  in
          let uu____27328 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27331 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___237_27327.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___237_27327.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27328;
            FStar_Syntax_Syntax.lbeff =
              (uu___237_27327.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27331;
            FStar_Syntax_Syntax.lbattrs =
              (uu___237_27327.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___237_27327.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27334 =
          let uu____27335 =
            let uu____27348 =
              let uu____27355 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27355)  in
            let uu____27364 = elim_delayed_subst_term t2  in
            (uu____27348, uu____27364)  in
          FStar_Syntax_Syntax.Tm_let uu____27335  in
        mk1 uu____27334
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27414 =
          let uu____27415 =
            let uu____27422 = elim_delayed_subst_term tm  in
            (uu____27422, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27415  in
        mk1 uu____27414
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27433 =
          let uu____27434 =
            let uu____27441 = elim_delayed_subst_term t2  in
            let uu____27444 = elim_delayed_subst_meta md  in
            (uu____27441, uu____27444)  in
          FStar_Syntax_Syntax.Tm_meta uu____27434  in
        mk1 uu____27433

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___119_27453  ->
         match uu___119_27453 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27457 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27457
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
        let uu____27480 =
          let uu____27481 =
            let uu____27490 = elim_delayed_subst_term t  in
            (uu____27490, uopt)  in
          FStar_Syntax_Syntax.Total uu____27481  in
        mk1 uu____27480
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27507 =
          let uu____27508 =
            let uu____27517 = elim_delayed_subst_term t  in
            (uu____27517, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27508  in
        mk1 uu____27507
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___238_27526 = ct  in
          let uu____27527 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27530 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27539 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___238_27526.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___238_27526.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27527;
            FStar_Syntax_Syntax.effect_args = uu____27530;
            FStar_Syntax_Syntax.flags = uu____27539
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___120_27542  ->
    match uu___120_27542 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____27554 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____27554
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27587 =
          let uu____27594 = elim_delayed_subst_term t  in (m, uu____27594)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27587
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27606 =
          let uu____27615 = elim_delayed_subst_term t  in
          (m1, m2, uu____27615)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27606
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27642  ->
         match uu____27642 with
         | (t,q) ->
             let uu____27653 = elim_delayed_subst_term t  in (uu____27653, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27673  ->
         match uu____27673 with
         | (x,q) ->
             let uu____27684 =
               let uu___239_27685 = x  in
               let uu____27686 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___239_27685.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___239_27685.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27686
               }  in
             (uu____27684, q)) bs

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
            | (uu____27778,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27804,FStar_Util.Inl t) ->
                let uu____27822 =
                  let uu____27829 =
                    let uu____27830 =
                      let uu____27843 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27843)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27830  in
                  FStar_Syntax_Syntax.mk uu____27829  in
                uu____27822 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27857 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27857 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27887 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27950 ->
                    let uu____27951 =
                      let uu____27960 =
                        let uu____27961 = FStar_Syntax_Subst.compress t4  in
                        uu____27961.FStar_Syntax_Syntax.n  in
                      (uu____27960, tc)  in
                    (match uu____27951 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27988) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____28029) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____28068,FStar_Util.Inl uu____28069) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____28096 -> failwith "Impossible")
                 in
              (match uu____27887 with
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
          let uu____28221 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28221 with
          | (univ_names1,binders1,tc) ->
              let uu____28287 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28287)
  
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
          let uu____28336 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28336 with
          | (univ_names1,binders1,tc) ->
              let uu____28402 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28402)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28441 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28441 with
           | (univ_names1,binders1,typ1) ->
               let uu___240_28475 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_28475.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_28475.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_28475.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_28475.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___241_28490 = s  in
          let uu____28491 =
            let uu____28492 =
              let uu____28501 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28501, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28492  in
          {
            FStar_Syntax_Syntax.sigel = uu____28491;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_28490.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_28490.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_28490.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_28490.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28518 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28518 with
           | (univ_names1,uu____28538,typ1) ->
               let uu___242_28556 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_28556.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_28556.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_28556.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_28556.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28562 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28562 with
           | (univ_names1,uu____28582,typ1) ->
               let uu___243_28600 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_28600.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_28600.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_28600.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_28600.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28628 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28628 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28653 =
                            let uu____28654 =
                              let uu____28655 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28655  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28654
                             in
                          elim_delayed_subst_term uu____28653  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___244_28658 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___244_28658.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___244_28658.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___244_28658.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___244_28658.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___245_28659 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___245_28659.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_28659.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_28659.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_28659.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___246_28665 = s  in
          let uu____28666 =
            let uu____28667 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28667  in
          {
            FStar_Syntax_Syntax.sigel = uu____28666;
            FStar_Syntax_Syntax.sigrng =
              (uu___246_28665.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_28665.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_28665.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_28665.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28671 = elim_uvars_aux_t env us [] t  in
          (match uu____28671 with
           | (us1,uu____28691,t1) ->
               let uu___247_28709 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___247_28709.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___247_28709.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___247_28709.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___247_28709.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28710 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28712 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28712 with
           | (univs1,binders,signature) ->
               let uu____28746 =
                 let uu____28751 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28751 with
                 | (univs_opening,univs2) ->
                     let uu____28774 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28774)
                  in
               (match uu____28746 with
                | (univs_opening,univs_closing) ->
                    let uu____28777 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28783 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28784 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28783, uu____28784)  in
                    (match uu____28777 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28808 =
                           match uu____28808 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28826 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28826 with
                                | (us1,t1) ->
                                    let uu____28837 =
                                      let uu____28846 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28857 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28846, uu____28857)  in
                                    (match uu____28837 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28886 =
                                           let uu____28895 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28906 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28895, uu____28906)  in
                                         (match uu____28886 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28936 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28936
                                                 in
                                              let uu____28937 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28937 with
                                               | (uu____28960,uu____28961,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28980 =
                                                       let uu____28981 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28981
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28980
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28990 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28990 with
                           | (uu____29007,uu____29008,t1) -> t1  in
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
                             | uu____29078 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____29103 =
                               let uu____29104 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____29104.FStar_Syntax_Syntax.n  in
                             match uu____29103 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____29163 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29194 =
                               let uu____29195 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29195.FStar_Syntax_Syntax.n  in
                             match uu____29194 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29216) ->
                                 let uu____29237 = destruct_action_body body
                                    in
                                 (match uu____29237 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____29282 ->
                                 let uu____29283 = destruct_action_body t  in
                                 (match uu____29283 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29332 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____29332 with
                           | (action_univs,t) ->
                               let uu____29341 = destruct_action_typ_templ t
                                  in
                               (match uu____29341 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___248_29382 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___248_29382.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___248_29382.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___249_29384 = ed  in
                           let uu____29385 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29386 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29387 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29388 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29389 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29390 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29391 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____29392 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____29393 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____29394 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29395 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____29396 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29397 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29398 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___249_29384.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___249_29384.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____29385;
                             FStar_Syntax_Syntax.bind_wp = uu____29386;
                             FStar_Syntax_Syntax.if_then_else = uu____29387;
                             FStar_Syntax_Syntax.ite_wp = uu____29388;
                             FStar_Syntax_Syntax.stronger = uu____29389;
                             FStar_Syntax_Syntax.close_wp = uu____29390;
                             FStar_Syntax_Syntax.assert_p = uu____29391;
                             FStar_Syntax_Syntax.assume_p = uu____29392;
                             FStar_Syntax_Syntax.null_wp = uu____29393;
                             FStar_Syntax_Syntax.trivial = uu____29394;
                             FStar_Syntax_Syntax.repr = uu____29395;
                             FStar_Syntax_Syntax.return_repr = uu____29396;
                             FStar_Syntax_Syntax.bind_repr = uu____29397;
                             FStar_Syntax_Syntax.actions = uu____29398;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___249_29384.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___250_29401 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___250_29401.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___250_29401.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___250_29401.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___250_29401.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___121_29422 =
            match uu___121_29422 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29453 = elim_uvars_aux_t env us [] t  in
                (match uu____29453 with
                 | (us1,uu____29481,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___251_29508 = sub_eff  in
            let uu____29509 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29512 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___251_29508.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___251_29508.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29509;
              FStar_Syntax_Syntax.lift = uu____29512
            }  in
          let uu___252_29515 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___252_29515.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___252_29515.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___252_29515.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___252_29515.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____29525 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29525 with
           | (univ_names1,binders1,comp1) ->
               let uu___253_29559 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___253_29559.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___253_29559.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___253_29559.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___253_29559.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29562 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29563 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  