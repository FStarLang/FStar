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
    let uu____7694 =
      let uu____7697 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7697  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7694  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7739 =
      let uu____7740 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7740  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7739
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7804 = arg_as_string a1  in
        (match uu____7804 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7810 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7810 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7823 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7823
              | uu____7824 -> FStar_Pervasives_Native.None)
         | uu____7829 -> FStar_Pervasives_Native.None)
    | uu____7832 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7852 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7852
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7889 =
          let uu____7910 = arg_as_string fn  in
          let uu____7913 = arg_as_int from_line  in
          let uu____7916 = arg_as_int from_col  in
          let uu____7919 = arg_as_int to_line  in
          let uu____7922 = arg_as_int to_col  in
          (uu____7910, uu____7913, uu____7916, uu____7919, uu____7922)  in
        (match uu____7889 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7953 =
                 let uu____7954 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7955 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7954 uu____7955  in
               let uu____7956 =
                 let uu____7957 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7958 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7957 uu____7958  in
               FStar_Range.mk_range fn1 uu____7953 uu____7956  in
             let uu____7959 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7959
         | uu____7960 -> FStar_Pervasives_Native.None)
    | uu____7981 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8014)::(a1,uu____8016)::(a2,uu____8018)::[] ->
        let uu____8055 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8055 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8060 -> FStar_Pervasives_Native.None)
    | uu____8061 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8092)::[] ->
        let uu____8101 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8101 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8107 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8107
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8108 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8134 =
      let uu____8151 =
        let uu____8168 =
          let uu____8185 =
            let uu____8202 =
              let uu____8219 =
                let uu____8236 =
                  let uu____8253 =
                    let uu____8270 =
                      let uu____8287 =
                        let uu____8304 =
                          let uu____8321 =
                            let uu____8338 =
                              let uu____8355 =
                                let uu____8372 =
                                  let uu____8389 =
                                    let uu____8406 =
                                      let uu____8423 =
                                        let uu____8440 =
                                          let uu____8457 =
                                            let uu____8474 =
                                              let uu____8491 =
                                                let uu____8506 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8506,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8515 =
                                                let uu____8532 =
                                                  let uu____8547 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8547,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8560 =
                                                  let uu____8577 =
                                                    let uu____8592 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8592,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8601 =
                                                    let uu____8618 =
                                                      let uu____8633 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8633,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8618]  in
                                                  uu____8577 :: uu____8601
                                                   in
                                                uu____8532 :: uu____8560  in
                                              uu____8491 :: uu____8515  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8474
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8457
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8440
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8423
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8406
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8853 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8853 y)))
                                    :: uu____8389
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8372
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8355
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8338
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8321
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8304
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8287
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9048 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9048)))
                      :: uu____8270
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9078 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9078)))
                    :: uu____8253
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9108 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9108)))
                  :: uu____8236
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9138 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9138)))
                :: uu____8219
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8202
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8185
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8168
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8151
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8134
     in
  let weak_ops =
    let uu____9293 =
      let uu____9308 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9308, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9293]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9388 =
        let uu____9393 =
          let uu____9394 = FStar_Syntax_Syntax.as_arg c  in [uu____9394]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9393  in
      uu____9388 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9468 =
                let uu____9483 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9483, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9505  ->
                          fun uu____9506  ->
                            match (uu____9505, uu____9506) with
                            | ((int_to_t1,x),(uu____9525,y)) ->
                                let uu____9535 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9535)))
                 in
              let uu____9536 =
                let uu____9553 =
                  let uu____9568 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9568, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9590  ->
                            fun uu____9591  ->
                              match (uu____9590, uu____9591) with
                              | ((int_to_t1,x),(uu____9610,y)) ->
                                  let uu____9620 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9620)))
                   in
                let uu____9621 =
                  let uu____9638 =
                    let uu____9653 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9653, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9675  ->
                              fun uu____9676  ->
                                match (uu____9675, uu____9676) with
                                | ((int_to_t1,x),(uu____9695,y)) ->
                                    let uu____9705 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9705)))
                     in
                  let uu____9706 =
                    let uu____9723 =
                      let uu____9738 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9738, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9756  ->
                                match uu____9756 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9723]  in
                  uu____9638 :: uu____9706  in
                uu____9553 :: uu____9621  in
              uu____9468 :: uu____9536))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9886 =
                let uu____9901 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9901, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9923  ->
                          fun uu____9924  ->
                            match (uu____9923, uu____9924) with
                            | ((int_to_t1,x),(uu____9943,y)) ->
                                let uu____9953 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9953)))
                 in
              let uu____9954 =
                let uu____9971 =
                  let uu____9986 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9986, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10008  ->
                            fun uu____10009  ->
                              match (uu____10008, uu____10009) with
                              | ((int_to_t1,x),(uu____10028,y)) ->
                                  let uu____10038 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10038)))
                   in
                [uu____9971]  in
              uu____9886 :: uu____9954))
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
    | (_typ,uu____10168)::(a1,uu____10170)::(a2,uu____10172)::[] ->
        let uu____10209 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10209 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10213 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10213.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10213.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10215 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10215.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10215.FStar_Syntax_Syntax.vars)
                })
         | uu____10216 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10218)::uu____10219::(a1,uu____10221)::(a2,uu____10223)::[]
        ->
        let uu____10272 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10272 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10276 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10276.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10276.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10278 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10278.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10278.FStar_Syntax_Syntax.vars)
                })
         | uu____10279 -> FStar_Pervasives_Native.None)
    | uu____10280 -> failwith "Unexpected number of arguments"  in
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
    let uu____10334 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10334 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10386 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10386) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10448  ->
           fun subst1  ->
             match uu____10448 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10489,uu____10490)) ->
                      let uu____10549 = b  in
                      (match uu____10549 with
                       | (bv,uu____10557) ->
                           let uu____10558 =
                             let uu____10559 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10559  in
                           if uu____10558
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10564 = unembed_binder term1  in
                              match uu____10564 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10571 =
                                      let uu___171_10572 = bv  in
                                      let uu____10573 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___171_10572.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___171_10572.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10573
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10571
                                     in
                                  let b_for_x =
                                    let uu____10577 =
                                      let uu____10584 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10584)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10577  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___111_10598  ->
                                         match uu___111_10598 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10599,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10601;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10602;_})
                                             ->
                                             let uu____10607 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10607
                                         | uu____10608 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10609 -> subst1)) env []
  
let reduce_primops :
  'Auu____10632 'Auu____10633 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10632) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10633 ->
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
            (let uu____10681 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10681 with
             | (head1,args) ->
                 let uu____10720 =
                   let uu____10721 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10721.FStar_Syntax_Syntax.n  in
                 (match uu____10720 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10727 = find_prim_step cfg fv  in
                      (match uu____10727 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10753  ->
                                   let uu____10754 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10755 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10762 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10754 uu____10755 uu____10762);
                              tm)
                           else
                             (let uu____10764 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10764 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10877  ->
                                        let uu____10878 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10878);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10881  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10883 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10883 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10891  ->
                                              let uu____10892 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10892);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10898  ->
                                              let uu____10899 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10900 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10899 uu____10900);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10901 ->
                           (log_primops cfg
                              (fun uu____10905  ->
                                 let uu____10906 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10906);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10910  ->
                            let uu____10911 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10911);
                       (match args with
                        | (a1,uu____10915)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10932 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10944  ->
                            let uu____10945 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10945);
                       (match args with
                        | (t,uu____10949)::(r,uu____10951)::[] ->
                            let uu____10978 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10978 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10984 -> tm))
                  | uu____10993 -> tm))
  
let reduce_equality :
  'Auu____11004 'Auu____11005 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11004) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11005 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_11051 = cfg  in
         {
           steps =
             (let uu___173_11054 = default_steps  in
              {
                beta = (uu___173_11054.beta);
                iota = (uu___173_11054.iota);
                zeta = (uu___173_11054.zeta);
                weak = (uu___173_11054.weak);
                hnf = (uu___173_11054.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___173_11054.do_not_unfold_pure_lets);
                unfold_until = (uu___173_11054.unfold_until);
                unfold_only = (uu___173_11054.unfold_only);
                unfold_fully = (uu___173_11054.unfold_fully);
                unfold_attr = (uu___173_11054.unfold_attr);
                unfold_tac = (uu___173_11054.unfold_tac);
                pure_subterms_within_computations =
                  (uu___173_11054.pure_subterms_within_computations);
                simplify = (uu___173_11054.simplify);
                erase_universes = (uu___173_11054.erase_universes);
                allow_unbound_universes =
                  (uu___173_11054.allow_unbound_universes);
                reify_ = (uu___173_11054.reify_);
                compress_uvars = (uu___173_11054.compress_uvars);
                no_full_norm = (uu___173_11054.no_full_norm);
                check_no_uvars = (uu___173_11054.check_no_uvars);
                unmeta = (uu___173_11054.unmeta);
                unascribe = (uu___173_11054.unascribe);
                in_full_norm_request = (uu___173_11054.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___173_11054.weakly_reduce_scrutinee)
              });
           tcenv = (uu___172_11051.tcenv);
           debug = (uu___172_11051.debug);
           delta_level = (uu___172_11051.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___172_11051.strong);
           memoize_lazy = (uu___172_11051.memoize_lazy);
           normalize_pure_lets = (uu___172_11051.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11061 .
    FStar_Syntax_Syntax.term -> 'Auu____11061 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11076 =
        let uu____11083 =
          let uu____11084 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11084.FStar_Syntax_Syntax.n  in
        (uu____11083, args)  in
      match uu____11076 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11090::uu____11091::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11095::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11100::uu____11101::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11104 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___112_11117  ->
    match uu___112_11117 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11123 =
          let uu____11126 =
            let uu____11127 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11127  in
          [uu____11126]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11123
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11133 =
          let uu____11136 =
            let uu____11137 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11137  in
          [uu____11136]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11133
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11160 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11160)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11211 =
            let uu____11216 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11216 s  in
          match uu____11211 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11232 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11232
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11258::(tm,uu____11260)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11289)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11310)::uu____11311::(tm,uu____11313)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11354 =
              let uu____11359 = full_norm steps  in parse_steps uu____11359
               in
            (match uu____11354 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11398 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___113_11417  ->
    match uu___113_11417 with
    | (App
        (uu____11420,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11421;
                       FStar_Syntax_Syntax.vars = uu____11422;_},uu____11423,uu____11424))::uu____11425
        -> true
    | uu____11430 -> false
  
let firstn :
  'Auu____11439 .
    Prims.int ->
      'Auu____11439 Prims.list ->
        ('Auu____11439 Prims.list,'Auu____11439 Prims.list)
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
          (uu____11481,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11482;
                         FStar_Syntax_Syntax.vars = uu____11483;_},uu____11484,uu____11485))::uu____11486
          -> (cfg.steps).reify_
      | uu____11491 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11514) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11524) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11543  ->
                  match uu____11543 with
                  | (a,uu____11551) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11557 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11582 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11583 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11598 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11599 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11600 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11601 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11602 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11603 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11610 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11617 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11630 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11647 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11660 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11667 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11729  ->
                   match uu____11729 with
                   | (a,uu____11737) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11744) ->
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
                     (fun uu____11866  ->
                        match uu____11866 with
                        | (a,uu____11874) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11879,uu____11880,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11886,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11892 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11899 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11900 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12192 ->
                   let uu____12217 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12217
               | uu____12218 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12226  ->
               let uu____12227 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12228 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12229 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12236 =
                 let uu____12237 =
                   let uu____12240 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12240
                    in
                 stack_to_string uu____12237  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12227 uu____12228 uu____12229 uu____12236);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12263 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12264 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12265 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12266;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____12267;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12270;
                 FStar_Syntax_Syntax.fv_delta = uu____12271;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12272;
                 FStar_Syntax_Syntax.fv_delta = uu____12273;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12274);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12281 ->
               let uu____12288 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12288
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12318 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12318)
               ->
               let cfg' =
                 let uu___174_12320 = cfg  in
                 {
                   steps =
                     (let uu___175_12323 = cfg.steps  in
                      {
                        beta = (uu___175_12323.beta);
                        iota = (uu___175_12323.iota);
                        zeta = (uu___175_12323.zeta);
                        weak = (uu___175_12323.weak);
                        hnf = (uu___175_12323.hnf);
                        primops = (uu___175_12323.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___175_12323.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___175_12323.unfold_attr);
                        unfold_tac = (uu___175_12323.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___175_12323.pure_subterms_within_computations);
                        simplify = (uu___175_12323.simplify);
                        erase_universes = (uu___175_12323.erase_universes);
                        allow_unbound_universes =
                          (uu___175_12323.allow_unbound_universes);
                        reify_ = (uu___175_12323.reify_);
                        compress_uvars = (uu___175_12323.compress_uvars);
                        no_full_norm = (uu___175_12323.no_full_norm);
                        check_no_uvars = (uu___175_12323.check_no_uvars);
                        unmeta = (uu___175_12323.unmeta);
                        unascribe = (uu___175_12323.unascribe);
                        in_full_norm_request =
                          (uu___175_12323.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___175_12323.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___174_12320.tcenv);
                   debug = (uu___174_12320.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___174_12320.primitive_steps);
                   strong = (uu___174_12320.strong);
                   memoize_lazy = (uu___174_12320.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12328 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____12328 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12357  ->
                              fun stack1  ->
                                match uu____12357 with
                                | (a,aq) ->
                                    let uu____12369 =
                                      let uu____12370 =
                                        let uu____12377 =
                                          let uu____12378 =
                                            let uu____12409 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12409, false)  in
                                          Clos uu____12378  in
                                        (uu____12377, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12370  in
                                    uu____12369 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12497  ->
                          let uu____12498 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12498);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12520 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___114_12525  ->
                                match uu___114_12525 with
                                | UnfoldUntil uu____12526 -> true
                                | UnfoldOnly uu____12527 -> true
                                | UnfoldFully uu____12530 -> true
                                | uu____12533 -> false))
                         in
                      if uu____12520
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___176_12538 = cfg  in
                      let uu____12539 =
                        let uu___177_12540 = to_fsteps s  in
                        {
                          beta = (uu___177_12540.beta);
                          iota = (uu___177_12540.iota);
                          zeta = (uu___177_12540.zeta);
                          weak = (uu___177_12540.weak);
                          hnf = (uu___177_12540.hnf);
                          primops = (uu___177_12540.primops);
                          do_not_unfold_pure_lets =
                            (uu___177_12540.do_not_unfold_pure_lets);
                          unfold_until = (uu___177_12540.unfold_until);
                          unfold_only = (uu___177_12540.unfold_only);
                          unfold_fully = (uu___177_12540.unfold_fully);
                          unfold_attr = (uu___177_12540.unfold_attr);
                          unfold_tac = (uu___177_12540.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___177_12540.pure_subterms_within_computations);
                          simplify = (uu___177_12540.simplify);
                          erase_universes = (uu___177_12540.erase_universes);
                          allow_unbound_universes =
                            (uu___177_12540.allow_unbound_universes);
                          reify_ = (uu___177_12540.reify_);
                          compress_uvars = (uu___177_12540.compress_uvars);
                          no_full_norm = (uu___177_12540.no_full_norm);
                          check_no_uvars = (uu___177_12540.check_no_uvars);
                          unmeta = (uu___177_12540.unmeta);
                          unascribe = (uu___177_12540.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___177_12540.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12539;
                        tcenv = (uu___176_12538.tcenv);
                        debug = (uu___176_12538.debug);
                        delta_level;
                        primitive_steps = (uu___176_12538.primitive_steps);
                        strong = (uu___176_12538.strong);
                        memoize_lazy = (uu___176_12538.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12545 =
                          let uu____12546 =
                            let uu____12551 = FStar_Util.now ()  in
                            (t1, uu____12551)  in
                          Debug uu____12546  in
                        uu____12545 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12555 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12555
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12564 =
                      let uu____12571 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12571, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12564  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12581 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12581  in
               let uu____12582 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12582
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12588  ->
                       let uu____12589 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12590 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12589 uu____12590);
                  if b
                  then
                    (let uu____12591 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12591 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12599 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12599) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12612),uu____12613);
                                FStar_Syntax_Syntax.sigrng = uu____12614;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12616;
                                FStar_Syntax_Syntax.sigattrs = uu____12617;_},uu____12618),uu____12619)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12678 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___115_12682  ->
                               match uu___115_12682 with
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
                          (let uu____12692 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12692))
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
                  let uu____12784 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12800 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12800 then (true, true) else (false, false)
                     in
                  match uu____12784 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12813  ->
                            let uu____12814 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12815 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12816 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12814 uu____12815 uu____12816);
                       if should_delta2
                       then
                         (let uu____12817 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___178_12833 = cfg  in
                                 {
                                   steps =
                                     (let uu___179_12836 = cfg.steps  in
                                      {
                                        beta = (uu___179_12836.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___179_12836.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___179_12836.unfold_attr);
                                        unfold_tac =
                                          (uu___179_12836.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___179_12836.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___179_12836.erase_universes);
                                        allow_unbound_universes =
                                          (uu___179_12836.allow_unbound_universes);
                                        reify_ = (uu___179_12836.reify_);
                                        compress_uvars =
                                          (uu___179_12836.compress_uvars);
                                        no_full_norm =
                                          (uu___179_12836.no_full_norm);
                                        check_no_uvars =
                                          (uu___179_12836.check_no_uvars);
                                        unmeta = (uu___179_12836.unmeta);
                                        unascribe =
                                          (uu___179_12836.unascribe);
                                        in_full_norm_request =
                                          (uu___179_12836.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___179_12836.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___178_12833.tcenv);
                                   debug = (uu___178_12833.debug);
                                   delta_level = (uu___178_12833.delta_level);
                                   primitive_steps =
                                     (uu___178_12833.primitive_steps);
                                   strong = (uu___178_12833.strong);
                                   memoize_lazy =
                                     (uu___178_12833.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___178_12833.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12817 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12852 = lookup_bvar env x  in
               (match uu____12852 with
                | Univ uu____12853 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12902 = FStar_ST.op_Bang r  in
                      (match uu____12902 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____13024  ->
                                 let uu____13025 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____13026 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____13025
                                   uu____13026);
                            (let uu____13027 = maybe_weakly_reduced t'  in
                             if uu____13027
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____13028 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13099)::uu____13100 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____13110,uu____13111))::stack_rest ->
                    (match c with
                     | Univ uu____13115 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13124 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13145  ->
                                    let uu____13146 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13146);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13174  ->
                                    let uu____13175 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13175);
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
                       (fun uu____13241  ->
                          let uu____13242 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13242);
                     norm cfg env stack1 t1)
                | (Match uu____13243)::uu____13244 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13258 = cfg.steps  in
                             {
                               beta = (uu___180_13258.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13258.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13258.unfold_until);
                               unfold_only = (uu___180_13258.unfold_only);
                               unfold_fully = (uu___180_13258.unfold_fully);
                               unfold_attr = (uu___180_13258.unfold_attr);
                               unfold_tac = (uu___180_13258.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13258.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13258.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13258.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13258.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13258.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13258.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13260 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13260.tcenv);
                               debug = (uu___181_13260.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13260.primitive_steps);
                               strong = (uu___181_13260.strong);
                               memoize_lazy = (uu___181_13260.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13260.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13262 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13262 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13294  -> dummy :: env1) env)
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
                                          let uu____13335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13342 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13342.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13342.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13343 -> lopt  in
                           (log cfg
                              (fun uu____13349  ->
                                 let uu____13350 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13350);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13359 = cfg  in
                               {
                                 steps = (uu___183_13359.steps);
                                 tcenv = (uu___183_13359.tcenv);
                                 debug = (uu___183_13359.debug);
                                 delta_level = (uu___183_13359.delta_level);
                                 primitive_steps =
                                   (uu___183_13359.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13359.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13359.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____13362)::uu____13363 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13373 = cfg.steps  in
                             {
                               beta = (uu___180_13373.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13373.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13373.unfold_until);
                               unfold_only = (uu___180_13373.unfold_only);
                               unfold_fully = (uu___180_13373.unfold_fully);
                               unfold_attr = (uu___180_13373.unfold_attr);
                               unfold_tac = (uu___180_13373.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13373.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13373.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13373.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13373.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13373.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13373.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13375 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13375.tcenv);
                               debug = (uu___181_13375.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13375.primitive_steps);
                               strong = (uu___181_13375.strong);
                               memoize_lazy = (uu___181_13375.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13375.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13377 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13377 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13409  -> dummy :: env1) env)
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
                                          let uu____13450 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13450)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13457 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13457.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13457.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13458 -> lopt  in
                           (log cfg
                              (fun uu____13464  ->
                                 let uu____13465 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13465);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13474 = cfg  in
                               {
                                 steps = (uu___183_13474.steps);
                                 tcenv = (uu___183_13474.tcenv);
                                 debug = (uu___183_13474.debug);
                                 delta_level = (uu___183_13474.delta_level);
                                 primitive_steps =
                                   (uu___183_13474.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13474.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13474.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13477)::uu____13478 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13490 = cfg.steps  in
                             {
                               beta = (uu___180_13490.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13490.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13490.unfold_until);
                               unfold_only = (uu___180_13490.unfold_only);
                               unfold_fully = (uu___180_13490.unfold_fully);
                               unfold_attr = (uu___180_13490.unfold_attr);
                               unfold_tac = (uu___180_13490.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13490.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13490.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13490.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13490.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13490.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13490.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13492 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13492.tcenv);
                               debug = (uu___181_13492.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13492.primitive_steps);
                               strong = (uu___181_13492.strong);
                               memoize_lazy = (uu___181_13492.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13492.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13494 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13494 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13526  -> dummy :: env1) env)
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
                                          let uu____13567 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13567)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13574 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13574.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13574.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13575 -> lopt  in
                           (log cfg
                              (fun uu____13581  ->
                                 let uu____13582 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13582);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13591 = cfg  in
                               {
                                 steps = (uu___183_13591.steps);
                                 tcenv = (uu___183_13591.tcenv);
                                 debug = (uu___183_13591.debug);
                                 delta_level = (uu___183_13591.delta_level);
                                 primitive_steps =
                                   (uu___183_13591.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13591.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13591.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13594)::uu____13595 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13609 = cfg.steps  in
                             {
                               beta = (uu___180_13609.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13609.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13609.unfold_until);
                               unfold_only = (uu___180_13609.unfold_only);
                               unfold_fully = (uu___180_13609.unfold_fully);
                               unfold_attr = (uu___180_13609.unfold_attr);
                               unfold_tac = (uu___180_13609.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13609.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13609.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13609.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13609.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13609.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13609.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13611 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13611.tcenv);
                               debug = (uu___181_13611.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13611.primitive_steps);
                               strong = (uu___181_13611.strong);
                               memoize_lazy = (uu___181_13611.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13611.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13613 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13613 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13645  -> dummy :: env1) env)
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
                                          let uu____13686 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13686)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13693 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13693.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13693.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13694 -> lopt  in
                           (log cfg
                              (fun uu____13700  ->
                                 let uu____13701 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13701);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13710 = cfg  in
                               {
                                 steps = (uu___183_13710.steps);
                                 tcenv = (uu___183_13710.tcenv);
                                 debug = (uu___183_13710.debug);
                                 delta_level = (uu___183_13710.delta_level);
                                 primitive_steps =
                                   (uu___183_13710.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13710.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13710.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13713)::uu____13714 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13728 = cfg.steps  in
                             {
                               beta = (uu___180_13728.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13728.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13728.unfold_until);
                               unfold_only = (uu___180_13728.unfold_only);
                               unfold_fully = (uu___180_13728.unfold_fully);
                               unfold_attr = (uu___180_13728.unfold_attr);
                               unfold_tac = (uu___180_13728.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13728.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13728.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13728.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13728.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13728.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13728.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13730 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13730.tcenv);
                               debug = (uu___181_13730.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13730.primitive_steps);
                               strong = (uu___181_13730.strong);
                               memoize_lazy = (uu___181_13730.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13730.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13732 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13732 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13764  -> dummy :: env1) env)
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
                                          let uu____13805 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13805)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13812 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13812.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13812.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13813 -> lopt  in
                           (log cfg
                              (fun uu____13819  ->
                                 let uu____13820 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13820);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13829 = cfg  in
                               {
                                 steps = (uu___183_13829.steps);
                                 tcenv = (uu___183_13829.tcenv);
                                 debug = (uu___183_13829.debug);
                                 delta_level = (uu___183_13829.delta_level);
                                 primitive_steps =
                                   (uu___183_13829.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13829.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13829.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13832)::uu____13833 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_13851 = cfg.steps  in
                             {
                               beta = (uu___180_13851.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13851.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13851.unfold_until);
                               unfold_only = (uu___180_13851.unfold_only);
                               unfold_fully = (uu___180_13851.unfold_fully);
                               unfold_attr = (uu___180_13851.unfold_attr);
                               unfold_tac = (uu___180_13851.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13851.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13851.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13851.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13851.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13851.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13851.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13853 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13853.tcenv);
                               debug = (uu___181_13853.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13853.primitive_steps);
                               strong = (uu___181_13853.strong);
                               memoize_lazy = (uu___181_13853.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13853.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13855 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13855 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13887  -> dummy :: env1) env)
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
                                          let uu____13928 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13928)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_13935 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_13935.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_13935.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13936 -> lopt  in
                           (log cfg
                              (fun uu____13942  ->
                                 let uu____13943 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13943);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_13952 = cfg  in
                               {
                                 steps = (uu___183_13952.steps);
                                 tcenv = (uu___183_13952.tcenv);
                                 debug = (uu___183_13952.debug);
                                 delta_level = (uu___183_13952.delta_level);
                                 primitive_steps =
                                   (uu___183_13952.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_13952.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_13952.normalize_pure_lets)
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
                             let uu___180_13958 = cfg.steps  in
                             {
                               beta = (uu___180_13958.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_13958.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_13958.unfold_until);
                               unfold_only = (uu___180_13958.unfold_only);
                               unfold_fully = (uu___180_13958.unfold_fully);
                               unfold_attr = (uu___180_13958.unfold_attr);
                               unfold_tac = (uu___180_13958.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_13958.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_13958.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_13958.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_13958.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_13958.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_13958.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_13960 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_13960.tcenv);
                               debug = (uu___181_13960.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_13960.primitive_steps);
                               strong = (uu___181_13960.strong);
                               memoize_lazy = (uu___181_13960.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_13960.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13962 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13962 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13994  -> dummy :: env1) env)
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
                                          let uu____14035 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14035)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14042 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14042.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14042.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14043 -> lopt  in
                           (log cfg
                              (fun uu____14049  ->
                                 let uu____14050 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14050);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14059 = cfg  in
                               {
                                 steps = (uu___183_14059.steps);
                                 tcenv = (uu___183_14059.tcenv);
                                 debug = (uu___183_14059.debug);
                                 delta_level = (uu___183_14059.delta_level);
                                 primitive_steps =
                                   (uu___183_14059.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14059.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14059.normalize_pure_lets)
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
                      (fun uu____14098  ->
                         fun stack1  ->
                           match uu____14098 with
                           | (a,aq) ->
                               let uu____14110 =
                                 let uu____14111 =
                                   let uu____14118 =
                                     let uu____14119 =
                                       let uu____14150 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____14150, false)  in
                                     Clos uu____14119  in
                                   (uu____14118, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____14111  in
                               uu____14110 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14238  ->
                     let uu____14239 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14239);
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
                             ((let uu___184_14285 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_14285.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_14285.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14286 ->
                      let uu____14301 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14301)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14304 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14304 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14329 =
                          let uu____14330 =
                            let uu____14337 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___185_14343 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___185_14343.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___185_14343.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14337)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14330  in
                        mk uu____14329 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14362 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14362
               else
                 (let uu____14364 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14364 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14372 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14394  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14372 c1  in
                      let t2 =
                        let uu____14416 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14416 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14527)::uu____14528 ->
                    (log cfg
                       (fun uu____14541  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14542)::uu____14543 ->
                    (log cfg
                       (fun uu____14554  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14555,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14556;
                                   FStar_Syntax_Syntax.vars = uu____14557;_},uu____14558,uu____14559))::uu____14560
                    ->
                    (log cfg
                       (fun uu____14567  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14568)::uu____14569 ->
                    (log cfg
                       (fun uu____14580  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14581 ->
                    (log cfg
                       (fun uu____14584  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14588  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14613 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14613
                         | FStar_Util.Inr c ->
                             let uu____14627 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14627
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14650 =
                               let uu____14651 =
                                 let uu____14678 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14678, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14651
                                in
                             mk uu____14650 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14713 ->
                           let uu____14714 =
                             let uu____14715 =
                               let uu____14716 =
                                 let uu____14743 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14743, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14716
                                in
                             mk uu____14715 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14714))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___186_14820 = cfg  in
                   {
                     steps =
                       (let uu___187_14823 = cfg.steps  in
                        {
                          beta = (uu___187_14823.beta);
                          iota = (uu___187_14823.iota);
                          zeta = (uu___187_14823.zeta);
                          weak = true;
                          hnf = (uu___187_14823.hnf);
                          primops = (uu___187_14823.primops);
                          do_not_unfold_pure_lets =
                            (uu___187_14823.do_not_unfold_pure_lets);
                          unfold_until = (uu___187_14823.unfold_until);
                          unfold_only = (uu___187_14823.unfold_only);
                          unfold_fully = (uu___187_14823.unfold_fully);
                          unfold_attr = (uu___187_14823.unfold_attr);
                          unfold_tac = (uu___187_14823.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___187_14823.pure_subterms_within_computations);
                          simplify = (uu___187_14823.simplify);
                          erase_universes = (uu___187_14823.erase_universes);
                          allow_unbound_universes =
                            (uu___187_14823.allow_unbound_universes);
                          reify_ = (uu___187_14823.reify_);
                          compress_uvars = (uu___187_14823.compress_uvars);
                          no_full_norm = (uu___187_14823.no_full_norm);
                          check_no_uvars = (uu___187_14823.check_no_uvars);
                          unmeta = (uu___187_14823.unmeta);
                          unascribe = (uu___187_14823.unascribe);
                          in_full_norm_request =
                            (uu___187_14823.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___187_14823.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___186_14820.tcenv);
                     debug = (uu___186_14820.debug);
                     delta_level = (uu___186_14820.delta_level);
                     primitive_steps = (uu___186_14820.primitive_steps);
                     strong = (uu___186_14820.strong);
                     memoize_lazy = (uu___186_14820.memoize_lazy);
                     normalize_pure_lets =
                       (uu___186_14820.normalize_pure_lets)
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
                         let uu____14859 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14859 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___188_14879 = cfg  in
                               let uu____14880 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___188_14879.steps);
                                 tcenv = uu____14880;
                                 debug = (uu___188_14879.debug);
                                 delta_level = (uu___188_14879.delta_level);
                                 primitive_steps =
                                   (uu___188_14879.primitive_steps);
                                 strong = (uu___188_14879.strong);
                                 memoize_lazy = (uu___188_14879.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_14879.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14887 =
                                 let uu____14888 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14888  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14887
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___189_14891 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___189_14891.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___189_14891.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___189_14891.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___189_14891.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14892 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14892
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14903,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14904;
                               FStar_Syntax_Syntax.lbunivs = uu____14905;
                               FStar_Syntax_Syntax.lbtyp = uu____14906;
                               FStar_Syntax_Syntax.lbeff = uu____14907;
                               FStar_Syntax_Syntax.lbdef = uu____14908;
                               FStar_Syntax_Syntax.lbattrs = uu____14909;
                               FStar_Syntax_Syntax.lbpos = uu____14910;_}::uu____14911),uu____14912)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14952 =
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
               if uu____14952
               then
                 let binder =
                   let uu____14954 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14954  in
                 let env1 =
                   let uu____14964 =
                     let uu____14971 =
                       let uu____14972 =
                         let uu____15003 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____15003,
                           false)
                          in
                       Clos uu____14972  in
                     ((FStar_Pervasives_Native.Some binder), uu____14971)  in
                   uu____14964 :: env  in
                 (log cfg
                    (fun uu____15098  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____15102  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____15103 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____15103))
                 else
                   (let uu____15105 =
                      let uu____15110 =
                        let uu____15111 =
                          let uu____15116 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____15116
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____15111]  in
                      FStar_Syntax_Subst.open_term uu____15110 body  in
                    match uu____15105 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____15137  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____15145 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____15145  in
                            FStar_Util.Inl
                              (let uu___190_15155 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___190_15155.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___190_15155.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____15158  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___191_15160 = lb  in
                             let uu____15161 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___191_15160.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___191_15160.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15161;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___191_15160.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___191_15160.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15186  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___192_15209 = cfg  in
                             {
                               steps = (uu___192_15209.steps);
                               tcenv = (uu___192_15209.tcenv);
                               debug = (uu___192_15209.debug);
                               delta_level = (uu___192_15209.delta_level);
                               primitive_steps =
                                 (uu___192_15209.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___192_15209.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___192_15209.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15212  ->
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
               let uu____15229 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15229 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15265 =
                               let uu___193_15266 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___193_15266.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___193_15266.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15265  in
                           let uu____15267 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15267 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15293 =
                                   FStar_List.map (fun uu____15309  -> dummy)
                                     lbs1
                                    in
                                 let uu____15310 =
                                   let uu____15319 =
                                     FStar_List.map
                                       (fun uu____15339  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15319 env  in
                                 FStar_List.append uu____15293 uu____15310
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15363 =
                                       let uu___194_15364 = rc  in
                                       let uu____15365 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___194_15364.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15365;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___194_15364.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15363
                                 | uu____15374 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___195_15380 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___195_15380.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___195_15380.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___195_15380.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___195_15380.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15390 =
                        FStar_List.map (fun uu____15406  -> dummy) lbs2  in
                      FStar_List.append uu____15390 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15414 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15414 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___196_15430 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___196_15430.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___196_15430.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15459 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15459
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15478 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15554  ->
                        match uu____15554 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___197_15675 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___197_15675.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___197_15675.FStar_Syntax_Syntax.sort)
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
               (match uu____15478 with
                | (rec_env,memos,uu____15902) ->
                    let uu____15955 =
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
                             let uu____16278 =
                               let uu____16285 =
                                 let uu____16286 =
                                   let uu____16317 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16317, false)
                                    in
                                 Clos uu____16286  in
                               (FStar_Pervasives_Native.None, uu____16285)
                                in
                             uu____16278 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16421  ->
                     let uu____16422 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16422);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16444 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16446::uu____16447 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16452) ->
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
                             | uu____16475 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16489 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16489
                              | uu____16500 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16506 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16532 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16548 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16563 =
                        let uu____16564 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16565 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16564 uu____16565
                         in
                      failwith uu____16563
                    else
                      (let uu____16567 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____16567)
                | uu____16568 -> norm cfg env stack t2))

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
                let uu____16578 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16578  in
              let uu____16579 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16579 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16592  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16603  ->
                        let uu____16604 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16605 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16604 uu____16605);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16610 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16610 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16619))::stack1 ->
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
                      | uu____16658 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16661 ->
                          let uu____16664 =
                            let uu____16665 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16665
                             in
                          failwith uu____16664
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
                  let uu___198_16689 = cfg  in
                  let uu____16690 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16690;
                    tcenv = (uu___198_16689.tcenv);
                    debug = (uu___198_16689.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___198_16689.primitive_steps);
                    strong = (uu___198_16689.strong);
                    memoize_lazy = (uu___198_16689.memoize_lazy);
                    normalize_pure_lets =
                      (uu___198_16689.normalize_pure_lets)
                  }
                else
                  (let uu___199_16692 = cfg  in
                   {
                     steps =
                       (let uu___200_16695 = cfg.steps  in
                        {
                          beta = (uu___200_16695.beta);
                          iota = (uu___200_16695.iota);
                          zeta = false;
                          weak = (uu___200_16695.weak);
                          hnf = (uu___200_16695.hnf);
                          primops = (uu___200_16695.primops);
                          do_not_unfold_pure_lets =
                            (uu___200_16695.do_not_unfold_pure_lets);
                          unfold_until = (uu___200_16695.unfold_until);
                          unfold_only = (uu___200_16695.unfold_only);
                          unfold_fully = (uu___200_16695.unfold_fully);
                          unfold_attr = (uu___200_16695.unfold_attr);
                          unfold_tac = (uu___200_16695.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___200_16695.pure_subterms_within_computations);
                          simplify = (uu___200_16695.simplify);
                          erase_universes = (uu___200_16695.erase_universes);
                          allow_unbound_universes =
                            (uu___200_16695.allow_unbound_universes);
                          reify_ = (uu___200_16695.reify_);
                          compress_uvars = (uu___200_16695.compress_uvars);
                          no_full_norm = (uu___200_16695.no_full_norm);
                          check_no_uvars = (uu___200_16695.check_no_uvars);
                          unmeta = (uu___200_16695.unmeta);
                          unascribe = (uu___200_16695.unascribe);
                          in_full_norm_request =
                            (uu___200_16695.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___200_16695.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___199_16692.tcenv);
                     debug = (uu___199_16692.debug);
                     delta_level = (uu___199_16692.delta_level);
                     primitive_steps = (uu___199_16692.primitive_steps);
                     strong = (uu___199_16692.strong);
                     memoize_lazy = (uu___199_16692.memoize_lazy);
                     normalize_pure_lets =
                       (uu___199_16692.normalize_pure_lets)
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
                  (fun uu____16729  ->
                     let uu____16730 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16731 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16730
                       uu____16731);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16733 =
                   let uu____16734 = FStar_Syntax_Subst.compress head3  in
                   uu____16734.FStar_Syntax_Syntax.n  in
                 match uu____16733 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16752 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16752
                        in
                     let uu____16753 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16753 with
                      | (uu____16754,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16764 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16774 =
                                   let uu____16775 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16775.FStar_Syntax_Syntax.n  in
                                 match uu____16774 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16781,uu____16782))
                                     ->
                                     let uu____16791 =
                                       let uu____16792 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16792.FStar_Syntax_Syntax.n  in
                                     (match uu____16791 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16798,msrc,uu____16800))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16809 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16809
                                      | uu____16810 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16811 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16812 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16812 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___201_16817 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___201_16817.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___201_16817.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___201_16817.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___201_16817.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___201_16817.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16818 = FStar_List.tl stack  in
                                    let uu____16819 =
                                      let uu____16820 =
                                        let uu____16827 =
                                          let uu____16828 =
                                            let uu____16841 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16841)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16828
                                           in
                                        FStar_Syntax_Syntax.mk uu____16827
                                         in
                                      uu____16820
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16818 uu____16819
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16857 =
                                      let uu____16858 = is_return body  in
                                      match uu____16858 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16862;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16863;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16866 -> false  in
                                    if uu____16857
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
                                         let uu____16887 =
                                           let uu____16894 =
                                             let uu____16895 =
                                               let uu____16912 =
                                                 let uu____16919 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16919]  in
                                               (uu____16912, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16895
                                              in
                                           FStar_Syntax_Syntax.mk uu____16894
                                            in
                                         uu____16887
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16953 =
                                           let uu____16954 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16954.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16953 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16960::uu____16961::[])
                                             ->
                                             let uu____16966 =
                                               let uu____16973 =
                                                 let uu____16974 =
                                                   let uu____16981 =
                                                     let uu____16982 =
                                                       let uu____16983 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16983
                                                        in
                                                     let uu____16984 =
                                                       let uu____16987 =
                                                         let uu____16988 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16988
                                                          in
                                                       [uu____16987]  in
                                                     uu____16982 ::
                                                       uu____16984
                                                      in
                                                   (bind1, uu____16981)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16974
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16973
                                                in
                                             uu____16966
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16994 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____17006 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____17006
                                         then
                                           let uu____17015 =
                                             let uu____17022 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17022
                                              in
                                           let uu____17023 =
                                             let uu____17032 =
                                               let uu____17039 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____17039
                                                in
                                             [uu____17032]  in
                                           uu____17015 :: uu____17023
                                         else []  in
                                       let reified =
                                         let uu____17068 =
                                           let uu____17075 =
                                             let uu____17076 =
                                               let uu____17091 =
                                                 let uu____17100 =
                                                   let uu____17109 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____17116 =
                                                     let uu____17125 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____17125]  in
                                                   uu____17109 :: uu____17116
                                                    in
                                                 let uu____17150 =
                                                   let uu____17159 =
                                                     let uu____17168 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____17175 =
                                                       let uu____17184 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____17191 =
                                                         let uu____17200 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____17207 =
                                                           let uu____17216 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____17216]  in
                                                         uu____17200 ::
                                                           uu____17207
                                                          in
                                                       uu____17184 ::
                                                         uu____17191
                                                        in
                                                     uu____17168 ::
                                                       uu____17175
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____17159
                                                    in
                                                 FStar_List.append
                                                   uu____17100 uu____17150
                                                  in
                                               (bind_inst, uu____17091)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____17076
                                              in
                                           FStar_Syntax_Syntax.mk uu____17075
                                            in
                                         uu____17068
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____17282  ->
                                            let uu____17283 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____17284 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____17283 uu____17284);
                                       (let uu____17285 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____17285 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____17309 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____17309
                        in
                     let uu____17310 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17310 with
                      | (uu____17311,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17348 =
                                  let uu____17349 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____17349.FStar_Syntax_Syntax.n  in
                                match uu____17348 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17353) -> t2
                                | uu____17358 -> head4  in
                              let uu____17359 =
                                let uu____17360 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17360.FStar_Syntax_Syntax.n  in
                              match uu____17359 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17366 -> FStar_Pervasives_Native.None
                               in
                            let uu____17367 = maybe_extract_fv head4  in
                            match uu____17367 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17377 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17377
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17382 = maybe_extract_fv head5
                                     in
                                  match uu____17382 with
                                  | FStar_Pervasives_Native.Some uu____17387
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17388 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17393 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17408 =
                              match uu____17408 with
                              | (e,q) ->
                                  let uu____17415 =
                                    let uu____17416 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17416.FStar_Syntax_Syntax.n  in
                                  (match uu____17415 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17431 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17431
                                   | uu____17432 -> false)
                               in
                            let uu____17433 =
                              let uu____17434 =
                                let uu____17443 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17443 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17434
                               in
                            if uu____17433
                            then
                              let uu____17462 =
                                let uu____17463 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17463
                                 in
                              failwith uu____17462
                            else ());
                           (let uu____17465 = maybe_unfold_action head_app
                               in
                            match uu____17465 with
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
                                   (fun uu____17508  ->
                                      let uu____17509 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17510 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17509 uu____17510);
                                 (let uu____17511 = FStar_List.tl stack  in
                                  norm cfg env uu____17511 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17513) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17537 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17537  in
                     (log cfg
                        (fun uu____17541  ->
                           let uu____17542 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17542);
                      (let uu____17543 = FStar_List.tl stack  in
                       norm cfg env uu____17543 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17664  ->
                               match uu____17664 with
                               | (pat,wopt,tm) ->
                                   let uu____17712 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17712)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17744 = FStar_List.tl stack  in
                     norm cfg env uu____17744 tm
                 | uu____17745 -> fallback ())

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
              (fun uu____17759  ->
                 let uu____17760 = FStar_Ident.string_of_lid msrc  in
                 let uu____17761 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17762 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17760
                   uu____17761 uu____17762);
            (let uu____17763 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17763
             then
               let ed =
                 let uu____17765 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17765  in
               let uu____17766 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17766 with
               | (uu____17767,return_repr) ->
                   let return_inst =
                     let uu____17780 =
                       let uu____17781 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17781.FStar_Syntax_Syntax.n  in
                     match uu____17780 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17787::[]) ->
                         let uu____17792 =
                           let uu____17799 =
                             let uu____17800 =
                               let uu____17807 =
                                 let uu____17808 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17808]  in
                               (return_tm, uu____17807)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17800  in
                           FStar_Syntax_Syntax.mk uu____17799  in
                         uu____17792 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17814 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17817 =
                     let uu____17824 =
                       let uu____17825 =
                         let uu____17840 =
                           let uu____17849 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17856 =
                             let uu____17865 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17865]  in
                           uu____17849 :: uu____17856  in
                         (return_inst, uu____17840)  in
                       FStar_Syntax_Syntax.Tm_app uu____17825  in
                     FStar_Syntax_Syntax.mk uu____17824  in
                   uu____17817 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17904 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17904 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17907 =
                      let uu____17908 = FStar_Ident.text_of_lid msrc  in
                      let uu____17909 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17908 uu____17909
                       in
                    failwith uu____17907
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17910;
                      FStar_TypeChecker_Env.mtarget = uu____17911;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17912;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17934 =
                      let uu____17935 = FStar_Ident.text_of_lid msrc  in
                      let uu____17936 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17935 uu____17936
                       in
                    failwith uu____17934
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17937;
                      FStar_TypeChecker_Env.mtarget = uu____17938;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17939;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17974 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17975 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17974 t FStar_Syntax_Syntax.tun uu____17975))

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
                (fun uu____18031  ->
                   match uu____18031 with
                   | (a,imp) ->
                       let uu____18042 = norm cfg env [] a  in
                       (uu____18042, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____18050  ->
             let uu____18051 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____18052 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____18051 uu____18052);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____18076 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____18076
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___202_18079 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___202_18079.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___202_18079.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____18101 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____18101
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___203_18104 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___203_18104.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___203_18104.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____18141  ->
                      match uu____18141 with
                      | (a,i) ->
                          let uu____18152 = norm cfg env [] a  in
                          (uu____18152, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___116_18170  ->
                       match uu___116_18170 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____18174 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____18174
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___204_18182 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___205_18185 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___205_18185.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___204_18182.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___204_18182.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____18188  ->
        match uu____18188 with
        | (x,imp) ->
            let uu____18191 =
              let uu___206_18192 = x  in
              let uu____18193 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___206_18192.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___206_18192.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18193
              }  in
            (uu____18191, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18199 =
          FStar_List.fold_left
            (fun uu____18233  ->
               fun b  ->
                 match uu____18233 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18199 with | (nbs,uu____18313) -> FStar_List.rev nbs

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
            let uu____18345 =
              let uu___207_18346 = rc  in
              let uu____18347 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___207_18346.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18347;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___207_18346.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18345
        | uu____18356 -> lopt

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
            (let uu____18377 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18378 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____18377
               uu____18378)
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
          let uu____18400 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18400
          then tm1
          else
            (let w t =
               let uu___208_18414 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___208_18414.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___208_18414.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18425 =
                 let uu____18426 = FStar_Syntax_Util.unmeta t  in
                 uu____18426.FStar_Syntax_Syntax.n  in
               match uu____18425 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18433 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18482)::args1,(bv,uu____18485)::bs1) ->
                   let uu____18519 =
                     let uu____18520 = FStar_Syntax_Subst.compress t  in
                     uu____18520.FStar_Syntax_Syntax.n  in
                   (match uu____18519 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18524 -> false)
               | ([],[]) -> true
               | (uu____18545,uu____18546) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18587 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18588 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18587
                    uu____18588)
               else ();
               (let uu____18590 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18590 with
                | (hd1,args) ->
                    let uu____18623 =
                      let uu____18624 = FStar_Syntax_Subst.compress hd1  in
                      uu____18624.FStar_Syntax_Syntax.n  in
                    (match uu____18623 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____18631 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18632 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18633 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18631 uu____18632 uu____18633)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18635 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18652 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18653 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18652
                    uu____18653)
               else ();
               (let uu____18655 = FStar_Syntax_Util.is_squash t  in
                match uu____18655 with
                | FStar_Pervasives_Native.Some (uu____18666,t') ->
                    is_applied bs t'
                | uu____18678 ->
                    let uu____18687 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18687 with
                     | FStar_Pervasives_Native.Some (uu____18698,t') ->
                         is_applied bs t'
                     | uu____18710 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18734 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18734 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18741)::(q,uu____18743)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18771 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18772 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18771 uu____18772)
                    else ();
                    (let uu____18774 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18774 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18779 =
                           let uu____18780 = FStar_Syntax_Subst.compress p
                              in
                           uu____18780.FStar_Syntax_Syntax.n  in
                         (match uu____18779 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18788 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18788))
                          | uu____18791 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18794)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18811 =
                           let uu____18812 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18812.FStar_Syntax_Syntax.n  in
                         (match uu____18811 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18820 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18820))
                          | uu____18823 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18827 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18827 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18832 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18832 with
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
                                     let uu____18843 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18843))
                               | uu____18846 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18851)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18868 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18868 with
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
                                     let uu____18879 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18879))
                               | uu____18882 -> FStar_Pervasives_Native.None)
                          | uu____18885 -> FStar_Pervasives_Native.None)
                     | uu____18888 -> FStar_Pervasives_Native.None))
               | uu____18891 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18904 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18904 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18910)::[],uu____18911,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18922 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18923 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18922
                         uu____18923)
                    else ();
                    is_quantified_const bv phi')
               | uu____18925 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18938 =
                 let uu____18939 = FStar_Syntax_Subst.compress phi  in
                 uu____18939.FStar_Syntax_Syntax.n  in
               match uu____18938 with
               | FStar_Syntax_Syntax.Tm_match (uu____18944,br::brs) ->
                   let uu____19011 = br  in
                   (match uu____19011 with
                    | (uu____19028,uu____19029,e) ->
                        let r =
                          let uu____19050 = simp_t e  in
                          match uu____19050 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____19056 =
                                FStar_List.for_all
                                  (fun uu____19074  ->
                                     match uu____19074 with
                                     | (uu____19087,uu____19088,e') ->
                                         let uu____19102 = simp_t e'  in
                                         uu____19102 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____19056
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____19110 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____19119 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____19119
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____19150 =
                 match uu____19150 with
                 | (t1,q) ->
                     let uu____19163 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____19163 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19191 -> (t1, q))
                  in
               let uu____19202 = FStar_Syntax_Util.head_and_args t  in
               match uu____19202 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19268 =
                 let uu____19269 = FStar_Syntax_Util.unmeta ty  in
                 uu____19269.FStar_Syntax_Syntax.n  in
               match uu____19268 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19273) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19278,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19298 -> false  in
             let simplify1 arg =
               let uu____19323 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19323, arg)  in
             let uu____19332 = is_forall_const tm1  in
             match uu____19332 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____19337 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19338 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19337
                       uu____19338)
                  else ();
                  (let uu____19340 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19340))
             | FStar_Pervasives_Native.None  ->
                 let uu____19341 =
                   let uu____19342 = FStar_Syntax_Subst.compress tm1  in
                   uu____19342.FStar_Syntax_Syntax.n  in
                 (match uu____19341 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19346;
                              FStar_Syntax_Syntax.vars = uu____19347;_},uu____19348);
                         FStar_Syntax_Syntax.pos = uu____19349;
                         FStar_Syntax_Syntax.vars = uu____19350;_},args)
                      ->
                      let uu____19376 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19376
                      then
                        let uu____19377 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19377 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19422)::
                             (uu____19423,(arg,uu____19425))::[] ->
                             maybe_auto_squash arg
                         | (uu____19474,(arg,uu____19476))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19477)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19526)::uu____19527::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19578::(FStar_Pervasives_Native.Some (false
                                         ),uu____19579)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19630 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19644 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19644
                         then
                           let uu____19645 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19645 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19690)::uu____19691::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19742::(FStar_Pervasives_Native.Some (true
                                           ),uu____19743)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19794)::(uu____19795,(arg,uu____19797))::[]
                               -> maybe_auto_squash arg
                           | (uu____19846,(arg,uu____19848))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19849)::[]
                               -> maybe_auto_squash arg
                           | uu____19898 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19912 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19912
                            then
                              let uu____19913 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19913 with
                              | uu____19958::(FStar_Pervasives_Native.Some
                                              (true ),uu____19959)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20010)::uu____20011::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20062)::(uu____20063,(arg,uu____20065))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20114,(p,uu____20116))::(uu____20117,
                                                                (q,uu____20119))::[]
                                  ->
                                  let uu____20166 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20166
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20168 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20182 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20182
                               then
                                 let uu____20183 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20183 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20228)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20229)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20280)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20281)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20332)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20333)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20384)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20385)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20436,(arg,uu____20438))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20439)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20488)::(uu____20489,(arg,uu____20491))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20540,(arg,uu____20542))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20543)::[]
                                     ->
                                     let uu____20592 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20592
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20593)::(uu____20594,(arg,uu____20596))::[]
                                     ->
                                     let uu____20645 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20645
                                 | (uu____20646,(p,uu____20648))::(uu____20649,
                                                                   (q,uu____20651))::[]
                                     ->
                                     let uu____20698 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20698
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20700 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20714 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20714
                                  then
                                    let uu____20715 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20715 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20760)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20791)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20822 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20836 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20836
                                     then
                                       match args with
                                       | (t,uu____20838)::[] ->
                                           let uu____20855 =
                                             let uu____20856 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20856.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20855 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20859::[],body,uu____20861)
                                                ->
                                                let uu____20888 = simp_t body
                                                   in
                                                (match uu____20888 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20891 -> tm1)
                                            | uu____20894 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20896))::(t,uu____20898)::[]
                                           ->
                                           let uu____20925 =
                                             let uu____20926 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20926.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20925 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20929::[],body,uu____20931)
                                                ->
                                                let uu____20958 = simp_t body
                                                   in
                                                (match uu____20958 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20961 -> tm1)
                                            | uu____20964 -> tm1)
                                       | uu____20965 -> tm1
                                     else
                                       (let uu____20975 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20975
                                        then
                                          match args with
                                          | (t,uu____20977)::[] ->
                                              let uu____20994 =
                                                let uu____20995 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20995.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20994 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20998::[],body,uu____21000)
                                                   ->
                                                   let uu____21027 =
                                                     simp_t body  in
                                                   (match uu____21027 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21030 -> tm1)
                                               | uu____21033 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21035))::(t,uu____21037)::[]
                                              ->
                                              let uu____21064 =
                                                let uu____21065 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21065.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21064 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21068::[],body,uu____21070)
                                                   ->
                                                   let uu____21097 =
                                                     simp_t body  in
                                                   (match uu____21097 with
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
                                                    | uu____21100 -> tm1)
                                               | uu____21103 -> tm1)
                                          | uu____21104 -> tm1
                                        else
                                          (let uu____21114 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21114
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21115;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21116;_},uu____21117)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21134;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21135;_},uu____21136)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21153 -> tm1
                                           else
                                             (let uu____21163 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____21163 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____21183 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21193;
                         FStar_Syntax_Syntax.vars = uu____21194;_},args)
                      ->
                      let uu____21216 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21216
                      then
                        let uu____21217 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21217 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21262)::
                             (uu____21263,(arg,uu____21265))::[] ->
                             maybe_auto_squash arg
                         | (uu____21314,(arg,uu____21316))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21317)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21366)::uu____21367::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21418::(FStar_Pervasives_Native.Some (false
                                         ),uu____21419)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21470 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21484 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21484
                         then
                           let uu____21485 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21485 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21530)::uu____21531::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21582::(FStar_Pervasives_Native.Some (true
                                           ),uu____21583)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21634)::(uu____21635,(arg,uu____21637))::[]
                               -> maybe_auto_squash arg
                           | (uu____21686,(arg,uu____21688))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21689)::[]
                               -> maybe_auto_squash arg
                           | uu____21738 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21752 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21752
                            then
                              let uu____21753 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21753 with
                              | uu____21798::(FStar_Pervasives_Native.Some
                                              (true ),uu____21799)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21850)::uu____21851::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21902)::(uu____21903,(arg,uu____21905))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21954,(p,uu____21956))::(uu____21957,
                                                                (q,uu____21959))::[]
                                  ->
                                  let uu____22006 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22006
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22008 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22022 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22022
                               then
                                 let uu____22023 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22023 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22068)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22069)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22120)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22121)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22172)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22173)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22224)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22225)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22276,(arg,uu____22278))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22279)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22328)::(uu____22329,(arg,uu____22331))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22380,(arg,uu____22382))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22383)::[]
                                     ->
                                     let uu____22432 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22432
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22433)::(uu____22434,(arg,uu____22436))::[]
                                     ->
                                     let uu____22485 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22485
                                 | (uu____22486,(p,uu____22488))::(uu____22489,
                                                                   (q,uu____22491))::[]
                                     ->
                                     let uu____22538 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22538
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22540 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22554 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22554
                                  then
                                    let uu____22555 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22555 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22600)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22631)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22662 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22676 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22676
                                     then
                                       match args with
                                       | (t,uu____22678)::[] ->
                                           let uu____22695 =
                                             let uu____22696 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22696.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22695 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22699::[],body,uu____22701)
                                                ->
                                                let uu____22728 = simp_t body
                                                   in
                                                (match uu____22728 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22731 -> tm1)
                                            | uu____22734 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22736))::(t,uu____22738)::[]
                                           ->
                                           let uu____22765 =
                                             let uu____22766 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22766.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22765 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22769::[],body,uu____22771)
                                                ->
                                                let uu____22798 = simp_t body
                                                   in
                                                (match uu____22798 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22801 -> tm1)
                                            | uu____22804 -> tm1)
                                       | uu____22805 -> tm1
                                     else
                                       (let uu____22815 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22815
                                        then
                                          match args with
                                          | (t,uu____22817)::[] ->
                                              let uu____22834 =
                                                let uu____22835 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22835.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22834 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22838::[],body,uu____22840)
                                                   ->
                                                   let uu____22867 =
                                                     simp_t body  in
                                                   (match uu____22867 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22870 -> tm1)
                                               | uu____22873 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22875))::(t,uu____22877)::[]
                                              ->
                                              let uu____22904 =
                                                let uu____22905 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22905.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22904 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22908::[],body,uu____22910)
                                                   ->
                                                   let uu____22937 =
                                                     simp_t body  in
                                                   (match uu____22937 with
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
                                                    | uu____22940 -> tm1)
                                               | uu____22943 -> tm1)
                                          | uu____22944 -> tm1
                                        else
                                          (let uu____22954 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22954
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22955;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22956;_},uu____22957)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22974;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22975;_},uu____22976)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22993 -> tm1
                                           else
                                             (let uu____23003 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____23003 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____23023 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23038 = simp_t t  in
                      (match uu____23038 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____23041 ->
                      let uu____23064 = is_const_match tm1  in
                      (match uu____23064 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____23067 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____23077  ->
               (let uu____23079 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23080 = FStar_Syntax_Print.term_to_string t  in
                let uu____23081 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23088 =
                  let uu____23089 =
                    let uu____23092 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23092
                     in
                  stack_to_string uu____23089  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23079 uu____23080 uu____23081 uu____23088);
               (let uu____23115 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23115
                then
                  let uu____23116 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23116 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23123 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23124 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23125 =
                          let uu____23126 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23126
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23123
                          uu____23124 uu____23125);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____23144 =
                     let uu____23145 =
                       let uu____23146 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____23146  in
                     FStar_Util.string_of_int uu____23145  in
                   let uu____23151 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____23152 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____23144 uu____23151 uu____23152)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____23158,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____23209  ->
                     let uu____23210 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____23210);
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
               let uu____23248 =
                 let uu___209_23249 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___209_23249.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___209_23249.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____23248
           | (Arg (Univ uu____23252,uu____23253,uu____23254))::uu____23255 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____23258,uu____23259))::uu____23260 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____23275,uu____23276),aq,r))::stack1
               when
               let uu____23326 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23326 ->
               let t2 =
                 let uu____23330 =
                   let uu____23335 =
                     let uu____23336 = closure_as_term cfg env_arg tm  in
                     (uu____23336, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____23335  in
                 uu____23330 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____23346),aq,r))::stack1 ->
               (log cfg
                  (fun uu____23399  ->
                     let uu____23400 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____23400);
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
                  (let uu____23412 = FStar_ST.op_Bang m  in
                   match uu____23412 with
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
                   | FStar_Pervasives_Native.Some (uu____23555,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23608 =
                 log cfg
                   (fun uu____23612  ->
                      let uu____23613 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23613);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23619 =
                 let uu____23620 = FStar_Syntax_Subst.compress t1  in
                 uu____23620.FStar_Syntax_Syntax.n  in
               (match uu____23619 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23647 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23647  in
                    (log cfg
                       (fun uu____23651  ->
                          let uu____23652 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23652);
                     (let uu____23653 = FStar_List.tl stack  in
                      norm cfg env1 uu____23653 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23654);
                       FStar_Syntax_Syntax.pos = uu____23655;
                       FStar_Syntax_Syntax.vars = uu____23656;_},(e,uu____23658)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23687 when
                    (cfg.steps).primops ->
                    let uu____23702 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23702 with
                     | (hd1,args) ->
                         let uu____23739 =
                           let uu____23740 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23740.FStar_Syntax_Syntax.n  in
                         (match uu____23739 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23744 = find_prim_step cfg fv  in
                              (match uu____23744 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23747; arity = uu____23748;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23750;
                                     requires_binder_substitution =
                                       uu____23751;
                                     interpretation = uu____23752;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23767 -> fallback " (3)" ())
                          | uu____23770 -> fallback " (4)" ()))
                | uu____23771 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23794  ->
                     let uu____23795 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23795);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23804 =
                   log cfg1
                     (fun uu____23809  ->
                        let uu____23810 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23811 =
                          let uu____23812 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23839  ->
                                    match uu____23839 with
                                    | (p,uu____23849,uu____23850) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23812
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23810 uu____23811);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___117_23867  ->
                                match uu___117_23867 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23868 -> false))
                         in
                      let steps =
                        let uu___210_23870 = cfg1.steps  in
                        {
                          beta = (uu___210_23870.beta);
                          iota = (uu___210_23870.iota);
                          zeta = false;
                          weak = (uu___210_23870.weak);
                          hnf = (uu___210_23870.hnf);
                          primops = (uu___210_23870.primops);
                          do_not_unfold_pure_lets =
                            (uu___210_23870.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___210_23870.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___210_23870.pure_subterms_within_computations);
                          simplify = (uu___210_23870.simplify);
                          erase_universes = (uu___210_23870.erase_universes);
                          allow_unbound_universes =
                            (uu___210_23870.allow_unbound_universes);
                          reify_ = (uu___210_23870.reify_);
                          compress_uvars = (uu___210_23870.compress_uvars);
                          no_full_norm = (uu___210_23870.no_full_norm);
                          check_no_uvars = (uu___210_23870.check_no_uvars);
                          unmeta = (uu___210_23870.unmeta);
                          unascribe = (uu___210_23870.unascribe);
                          in_full_norm_request =
                            (uu___210_23870.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___210_23870.weakly_reduce_scrutinee)
                        }  in
                      let uu___211_23875 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___211_23875.tcenv);
                        debug = (uu___211_23875.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___211_23875.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___211_23875.memoize_lazy);
                        normalize_pure_lets =
                          (uu___211_23875.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23947 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23976 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____24060  ->
                                    fun uu____24061  ->
                                      match (uu____24060, uu____24061) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____24200 = norm_pat env3 p1
                                             in
                                          (match uu____24200 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23976 with
                           | (pats1,env3) ->
                               ((let uu___212_24362 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___212_24362.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___213_24381 = x  in
                            let uu____24382 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___213_24381.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___213_24381.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24382
                            }  in
                          ((let uu___214_24396 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___214_24396.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___215_24407 = x  in
                            let uu____24408 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___215_24407.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___215_24407.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24408
                            }  in
                          ((let uu___216_24422 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___216_24422.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___217_24438 = x  in
                            let uu____24439 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___217_24438.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___217_24438.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24439
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___218_24454 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___218_24454.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24498 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24528 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24528 with
                                  | (p,wopt,e) ->
                                      let uu____24548 = norm_pat env1 p  in
                                      (match uu____24548 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24603 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24603
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24620 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24620
                      then
                        norm
                          (let uu___219_24625 = cfg1  in
                           {
                             steps =
                               (let uu___220_24628 = cfg1.steps  in
                                {
                                  beta = (uu___220_24628.beta);
                                  iota = (uu___220_24628.iota);
                                  zeta = (uu___220_24628.zeta);
                                  weak = (uu___220_24628.weak);
                                  hnf = (uu___220_24628.hnf);
                                  primops = (uu___220_24628.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___220_24628.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___220_24628.unfold_until);
                                  unfold_only = (uu___220_24628.unfold_only);
                                  unfold_fully =
                                    (uu___220_24628.unfold_fully);
                                  unfold_attr = (uu___220_24628.unfold_attr);
                                  unfold_tac = (uu___220_24628.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___220_24628.pure_subterms_within_computations);
                                  simplify = (uu___220_24628.simplify);
                                  erase_universes =
                                    (uu___220_24628.erase_universes);
                                  allow_unbound_universes =
                                    (uu___220_24628.allow_unbound_universes);
                                  reify_ = (uu___220_24628.reify_);
                                  compress_uvars =
                                    (uu___220_24628.compress_uvars);
                                  no_full_norm =
                                    (uu___220_24628.no_full_norm);
                                  check_no_uvars =
                                    (uu___220_24628.check_no_uvars);
                                  unmeta = (uu___220_24628.unmeta);
                                  unascribe = (uu___220_24628.unascribe);
                                  in_full_norm_request =
                                    (uu___220_24628.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___219_24625.tcenv);
                             debug = (uu___219_24625.debug);
                             delta_level = (uu___219_24625.delta_level);
                             primitive_steps =
                               (uu___219_24625.primitive_steps);
                             strong = (uu___219_24625.strong);
                             memoize_lazy = (uu___219_24625.memoize_lazy);
                             normalize_pure_lets =
                               (uu___219_24625.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24630 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24630)
                    in
                 let rec is_cons head1 =
                   let uu____24655 =
                     let uu____24656 = FStar_Syntax_Subst.compress head1  in
                     uu____24656.FStar_Syntax_Syntax.n  in
                   match uu____24655 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24660) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24665 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24666;
                         FStar_Syntax_Syntax.fv_delta = uu____24667;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24668;
                         FStar_Syntax_Syntax.fv_delta = uu____24669;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24670);_}
                       -> true
                   | uu____24677 -> false  in
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
                   let uu____24840 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24840 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24927 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24966 ->
                                 let uu____24967 =
                                   let uu____24968 = is_cons head1  in
                                   Prims.op_Negation uu____24968  in
                                 FStar_Util.Inr uu____24967)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24993 =
                              let uu____24994 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24994.FStar_Syntax_Syntax.n  in
                            (match uu____24993 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____25012 ->
                                 let uu____25013 =
                                   let uu____25014 = is_cons head1  in
                                   Prims.op_Negation uu____25014  in
                                 FStar_Util.Inr uu____25013))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____25091)::rest_a,(p1,uu____25094)::rest_p) ->
                       let uu____25138 = matches_pat t2 p1  in
                       (match uu____25138 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____25187 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____25305 = matches_pat scrutinee1 p1  in
                       (match uu____25305 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____25345  ->
                                  let uu____25346 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____25347 =
                                    let uu____25348 =
                                      FStar_List.map
                                        (fun uu____25358  ->
                                           match uu____25358 with
                                           | (uu____25363,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____25348
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____25346 uu____25347);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____25395  ->
                                       match uu____25395 with
                                       | (bv,t2) ->
                                           let uu____25418 =
                                             let uu____25425 =
                                               let uu____25428 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____25428
                                                in
                                             let uu____25429 =
                                               let uu____25430 =
                                                 let uu____25461 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____25461, false)
                                                  in
                                               Clos uu____25430  in
                                             (uu____25425, uu____25429)  in
                                           uu____25418 :: env2) env1 s
                                 in
                              let uu____25574 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25574)))
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
    let uu____25601 =
      let uu____25604 = FStar_ST.op_Bang plugins  in p :: uu____25604  in
    FStar_ST.op_Colon_Equals plugins uu____25601  in
  let retrieve uu____25712 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25789  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___118_25830  ->
                  match uu___118_25830 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25834 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25840 -> d  in
        let uu____25843 = to_fsteps s  in
        let uu____25844 =
          let uu____25845 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25846 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25847 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25848 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____25849 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25850 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25845;
            primop = uu____25846;
            b380 = uu____25847;
            wpe = uu____25848;
            norm_delayed = uu____25849;
            print_normalized = uu____25850
          }  in
        let uu____25851 =
          let uu____25854 =
            let uu____25857 = retrieve_plugins ()  in
            FStar_List.append uu____25857 psteps  in
          add_steps built_in_primitive_steps uu____25854  in
        let uu____25860 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25862 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25862)
           in
        {
          steps = uu____25843;
          tcenv = e;
          debug = uu____25844;
          delta_level = d1;
          primitive_steps = uu____25851;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25860
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
      fun t  -> let uu____25944 = config s e  in norm_comp uu____25944 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25961 = config [] env  in norm_universe uu____25961 [] u
  
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
        let uu____25985 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25985  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25992 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___221_26011 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___221_26011.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___221_26011.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____26018 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26018
          then
            let ct1 =
              let uu____26020 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26020 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____26027 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26027
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___222_26031 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___222_26031.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___222_26031.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___222_26031.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___223_26033 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___223_26033.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___223_26033.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___223_26033.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___223_26033.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___224_26034 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___224_26034.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___224_26034.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26036 -> c
  
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
        let uu____26054 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____26054  in
      let uu____26061 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____26061
      then
        let uu____26062 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____26062 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____26068  ->
                 let uu____26069 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____26069)
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
            ((let uu____26090 =
                let uu____26095 =
                  let uu____26096 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26096
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26095)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26090);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____26111 = config [AllowUnboundUniverses] env  in
          norm_comp uu____26111 [] c
        with
        | e ->
            ((let uu____26124 =
                let uu____26129 =
                  let uu____26130 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26130
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26129)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26124);
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
                   let uu____26175 =
                     let uu____26176 =
                       let uu____26183 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26183)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26176  in
                   mk uu____26175 t01.FStar_Syntax_Syntax.pos
               | uu____26188 -> t2)
          | uu____26189 -> t2  in
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
        let uu____26253 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26253 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26282 ->
                 let uu____26289 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26289 with
                  | (actuals,uu____26299,uu____26300) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26314 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26314 with
                         | (binders,args) ->
                             let uu____26325 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26325
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
      | uu____26339 ->
          let uu____26340 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26340 with
           | (head1,args) ->
               let uu____26377 =
                 let uu____26378 = FStar_Syntax_Subst.compress head1  in
                 uu____26378.FStar_Syntax_Syntax.n  in
               (match uu____26377 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26403 =
                      let uu____26416 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26416  in
                    (match uu____26403 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26446 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___229_26454 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___229_26454.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___229_26454.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___229_26454.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___229_26454.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___229_26454.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___229_26454.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___229_26454.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___229_26454.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___229_26454.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___229_26454.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___229_26454.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___229_26454.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___229_26454.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___229_26454.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___229_26454.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___229_26454.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___229_26454.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___229_26454.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___229_26454.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___229_26454.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___229_26454.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___229_26454.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___229_26454.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___229_26454.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___229_26454.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___229_26454.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___229_26454.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___229_26454.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___229_26454.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___229_26454.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___229_26454.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___229_26454.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___229_26454.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___229_26454.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___229_26454.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___229_26454.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____26446 with
                            | (uu____26455,ty,uu____26457) ->
                                eta_expand_with_type env t ty))
                | uu____26458 ->
                    let uu____26459 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___230_26467 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___230_26467.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___230_26467.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___230_26467.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___230_26467.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___230_26467.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___230_26467.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___230_26467.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___230_26467.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___230_26467.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___230_26467.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___230_26467.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___230_26467.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___230_26467.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___230_26467.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___230_26467.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___230_26467.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___230_26467.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___230_26467.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___230_26467.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___230_26467.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___230_26467.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___230_26467.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___230_26467.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___230_26467.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___230_26467.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___230_26467.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___230_26467.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___230_26467.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___230_26467.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___230_26467.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___230_26467.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___230_26467.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___230_26467.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___230_26467.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___230_26467.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___230_26467.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____26459 with
                     | (uu____26468,ty,uu____26470) ->
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
      let uu___231_26543 = x  in
      let uu____26544 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___231_26543.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___231_26543.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26544
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26547 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26572 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26573 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26574 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26575 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26582 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26583 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26584 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___232_26614 = rc  in
          let uu____26615 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26624 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___232_26614.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26615;
            FStar_Syntax_Syntax.residual_flags = uu____26624
          }  in
        let uu____26627 =
          let uu____26628 =
            let uu____26645 = elim_delayed_subst_binders bs  in
            let uu____26652 = elim_delayed_subst_term t2  in
            let uu____26655 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26645, uu____26652, uu____26655)  in
          FStar_Syntax_Syntax.Tm_abs uu____26628  in
        mk1 uu____26627
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26686 =
          let uu____26687 =
            let uu____26700 = elim_delayed_subst_binders bs  in
            let uu____26707 = elim_delayed_subst_comp c  in
            (uu____26700, uu____26707)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26687  in
        mk1 uu____26686
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26724 =
          let uu____26725 =
            let uu____26732 = elim_bv bv  in
            let uu____26733 = elim_delayed_subst_term phi  in
            (uu____26732, uu____26733)  in
          FStar_Syntax_Syntax.Tm_refine uu____26725  in
        mk1 uu____26724
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26760 =
          let uu____26761 =
            let uu____26776 = elim_delayed_subst_term t2  in
            let uu____26779 = elim_delayed_subst_args args  in
            (uu____26776, uu____26779)  in
          FStar_Syntax_Syntax.Tm_app uu____26761  in
        mk1 uu____26760
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___233_26847 = p  in
              let uu____26848 =
                let uu____26849 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26849  in
              {
                FStar_Syntax_Syntax.v = uu____26848;
                FStar_Syntax_Syntax.p =
                  (uu___233_26847.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___234_26851 = p  in
              let uu____26852 =
                let uu____26853 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26853  in
              {
                FStar_Syntax_Syntax.v = uu____26852;
                FStar_Syntax_Syntax.p =
                  (uu___234_26851.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___235_26860 = p  in
              let uu____26861 =
                let uu____26862 =
                  let uu____26869 = elim_bv x  in
                  let uu____26870 = elim_delayed_subst_term t0  in
                  (uu____26869, uu____26870)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26862  in
              {
                FStar_Syntax_Syntax.v = uu____26861;
                FStar_Syntax_Syntax.p =
                  (uu___235_26860.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___236_26893 = p  in
              let uu____26894 =
                let uu____26895 =
                  let uu____26908 =
                    FStar_List.map
                      (fun uu____26931  ->
                         match uu____26931 with
                         | (x,b) ->
                             let uu____26944 = elim_pat x  in
                             (uu____26944, b)) pats
                     in
                  (fv, uu____26908)  in
                FStar_Syntax_Syntax.Pat_cons uu____26895  in
              {
                FStar_Syntax_Syntax.v = uu____26894;
                FStar_Syntax_Syntax.p =
                  (uu___236_26893.FStar_Syntax_Syntax.p)
              }
          | uu____26957 -> p  in
        let elim_branch uu____26981 =
          match uu____26981 with
          | (pat,wopt,t3) ->
              let uu____27007 = elim_pat pat  in
              let uu____27010 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27013 = elim_delayed_subst_term t3  in
              (uu____27007, uu____27010, uu____27013)
           in
        let uu____27018 =
          let uu____27019 =
            let uu____27042 = elim_delayed_subst_term t2  in
            let uu____27045 = FStar_List.map elim_branch branches  in
            (uu____27042, uu____27045)  in
          FStar_Syntax_Syntax.Tm_match uu____27019  in
        mk1 uu____27018
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____27176 =
          match uu____27176 with
          | (tc,topt) ->
              let uu____27211 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27221 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27221
                | FStar_Util.Inr c ->
                    let uu____27223 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27223
                 in
              let uu____27224 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27211, uu____27224)
           in
        let uu____27233 =
          let uu____27234 =
            let uu____27261 = elim_delayed_subst_term t2  in
            let uu____27264 = elim_ascription a  in
            (uu____27261, uu____27264, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27234  in
        mk1 uu____27233
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___237_27325 = lb  in
          let uu____27326 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27329 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___237_27325.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___237_27325.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27326;
            FStar_Syntax_Syntax.lbeff =
              (uu___237_27325.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27329;
            FStar_Syntax_Syntax.lbattrs =
              (uu___237_27325.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___237_27325.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27332 =
          let uu____27333 =
            let uu____27346 =
              let uu____27353 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27353)  in
            let uu____27362 = elim_delayed_subst_term t2  in
            (uu____27346, uu____27362)  in
          FStar_Syntax_Syntax.Tm_let uu____27333  in
        mk1 uu____27332
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27412 =
          let uu____27413 =
            let uu____27420 = elim_delayed_subst_term tm  in
            (uu____27420, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27413  in
        mk1 uu____27412
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27431 =
          let uu____27432 =
            let uu____27439 = elim_delayed_subst_term t2  in
            let uu____27442 = elim_delayed_subst_meta md  in
            (uu____27439, uu____27442)  in
          FStar_Syntax_Syntax.Tm_meta uu____27432  in
        mk1 uu____27431

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___119_27451  ->
         match uu___119_27451 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27455 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27455
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
        let uu____27478 =
          let uu____27479 =
            let uu____27488 = elim_delayed_subst_term t  in
            (uu____27488, uopt)  in
          FStar_Syntax_Syntax.Total uu____27479  in
        mk1 uu____27478
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27505 =
          let uu____27506 =
            let uu____27515 = elim_delayed_subst_term t  in
            (uu____27515, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27506  in
        mk1 uu____27505
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___238_27524 = ct  in
          let uu____27525 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27528 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27537 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___238_27524.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___238_27524.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27525;
            FStar_Syntax_Syntax.effect_args = uu____27528;
            FStar_Syntax_Syntax.flags = uu____27537
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___120_27540  ->
    match uu___120_27540 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____27552 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____27552
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27585 =
          let uu____27592 = elim_delayed_subst_term t  in (m, uu____27592)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27585
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27604 =
          let uu____27613 = elim_delayed_subst_term t  in
          (m1, m2, uu____27613)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27604
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27640  ->
         match uu____27640 with
         | (t,q) ->
             let uu____27651 = elim_delayed_subst_term t  in (uu____27651, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27671  ->
         match uu____27671 with
         | (x,q) ->
             let uu____27682 =
               let uu___239_27683 = x  in
               let uu____27684 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___239_27683.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___239_27683.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27684
               }  in
             (uu____27682, q)) bs

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
            | (uu____27776,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27802,FStar_Util.Inl t) ->
                let uu____27820 =
                  let uu____27827 =
                    let uu____27828 =
                      let uu____27841 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27841)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27828  in
                  FStar_Syntax_Syntax.mk uu____27827  in
                uu____27820 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27855 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27855 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27885 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27948 ->
                    let uu____27949 =
                      let uu____27958 =
                        let uu____27959 = FStar_Syntax_Subst.compress t4  in
                        uu____27959.FStar_Syntax_Syntax.n  in
                      (uu____27958, tc)  in
                    (match uu____27949 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27986) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____28027) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____28066,FStar_Util.Inl uu____28067) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____28094 -> failwith "Impossible")
                 in
              (match uu____27885 with
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
          let uu____28219 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28219 with
          | (univ_names1,binders1,tc) ->
              let uu____28285 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28285)
  
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
          let uu____28334 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28334 with
          | (univ_names1,binders1,tc) ->
              let uu____28400 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28400)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28439 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28439 with
           | (univ_names1,binders1,typ1) ->
               let uu___240_28473 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_28473.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_28473.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_28473.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_28473.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___241_28488 = s  in
          let uu____28489 =
            let uu____28490 =
              let uu____28499 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28499, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28490  in
          {
            FStar_Syntax_Syntax.sigel = uu____28489;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_28488.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_28488.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_28488.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_28488.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28516 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28516 with
           | (univ_names1,uu____28536,typ1) ->
               let uu___242_28554 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_28554.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_28554.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_28554.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_28554.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28560 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28560 with
           | (univ_names1,uu____28580,typ1) ->
               let uu___243_28598 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_28598.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_28598.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_28598.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_28598.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28626 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28626 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28651 =
                            let uu____28652 =
                              let uu____28653 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28653  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28652
                             in
                          elim_delayed_subst_term uu____28651  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___244_28656 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___244_28656.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___244_28656.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___244_28656.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___244_28656.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___245_28657 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___245_28657.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_28657.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_28657.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_28657.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___246_28663 = s  in
          let uu____28664 =
            let uu____28665 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28665  in
          {
            FStar_Syntax_Syntax.sigel = uu____28664;
            FStar_Syntax_Syntax.sigrng =
              (uu___246_28663.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_28663.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_28663.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_28663.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28669 = elim_uvars_aux_t env us [] t  in
          (match uu____28669 with
           | (us1,uu____28689,t1) ->
               let uu___247_28707 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___247_28707.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___247_28707.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___247_28707.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___247_28707.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28708 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28710 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28710 with
           | (univs1,binders,signature) ->
               let uu____28744 =
                 let uu____28749 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28749 with
                 | (univs_opening,univs2) ->
                     let uu____28772 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28772)
                  in
               (match uu____28744 with
                | (univs_opening,univs_closing) ->
                    let uu____28775 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28781 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28782 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28781, uu____28782)  in
                    (match uu____28775 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28806 =
                           match uu____28806 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28824 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28824 with
                                | (us1,t1) ->
                                    let uu____28835 =
                                      let uu____28844 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28855 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28844, uu____28855)  in
                                    (match uu____28835 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28884 =
                                           let uu____28893 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28904 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28893, uu____28904)  in
                                         (match uu____28884 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28934 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28934
                                                 in
                                              let uu____28935 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28935 with
                                               | (uu____28958,uu____28959,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28978 =
                                                       let uu____28979 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28979
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28978
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28988 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28988 with
                           | (uu____29005,uu____29006,t1) -> t1  in
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
                             | uu____29076 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____29101 =
                               let uu____29102 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____29102.FStar_Syntax_Syntax.n  in
                             match uu____29101 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____29161 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29192 =
                               let uu____29193 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29193.FStar_Syntax_Syntax.n  in
                             match uu____29192 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29214) ->
                                 let uu____29235 = destruct_action_body body
                                    in
                                 (match uu____29235 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____29280 ->
                                 let uu____29281 = destruct_action_body t  in
                                 (match uu____29281 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29330 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____29330 with
                           | (action_univs,t) ->
                               let uu____29339 = destruct_action_typ_templ t
                                  in
                               (match uu____29339 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___248_29380 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___248_29380.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___248_29380.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___249_29382 = ed  in
                           let uu____29383 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29384 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29385 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29386 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29387 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29388 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29389 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____29390 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____29391 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____29392 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29393 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____29394 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29395 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29396 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___249_29382.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___249_29382.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____29383;
                             FStar_Syntax_Syntax.bind_wp = uu____29384;
                             FStar_Syntax_Syntax.if_then_else = uu____29385;
                             FStar_Syntax_Syntax.ite_wp = uu____29386;
                             FStar_Syntax_Syntax.stronger = uu____29387;
                             FStar_Syntax_Syntax.close_wp = uu____29388;
                             FStar_Syntax_Syntax.assert_p = uu____29389;
                             FStar_Syntax_Syntax.assume_p = uu____29390;
                             FStar_Syntax_Syntax.null_wp = uu____29391;
                             FStar_Syntax_Syntax.trivial = uu____29392;
                             FStar_Syntax_Syntax.repr = uu____29393;
                             FStar_Syntax_Syntax.return_repr = uu____29394;
                             FStar_Syntax_Syntax.bind_repr = uu____29395;
                             FStar_Syntax_Syntax.actions = uu____29396;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___249_29382.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___250_29399 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___250_29399.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___250_29399.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___250_29399.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___250_29399.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___121_29420 =
            match uu___121_29420 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29451 = elim_uvars_aux_t env us [] t  in
                (match uu____29451 with
                 | (us1,uu____29479,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___251_29506 = sub_eff  in
            let uu____29507 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29510 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___251_29506.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___251_29506.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29507;
              FStar_Syntax_Syntax.lift = uu____29510
            }  in
          let uu___252_29513 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___252_29513.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___252_29513.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___252_29513.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___252_29513.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____29523 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29523 with
           | (univ_names1,binders1,comp1) ->
               let uu___253_29557 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___253_29557.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___253_29557.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___253_29557.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___253_29557.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29560 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29561 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  