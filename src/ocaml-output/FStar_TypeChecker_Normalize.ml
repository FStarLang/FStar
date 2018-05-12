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
                             (let uu___154_4887 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_4887.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_4887.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4871))
                       in
                    (match uu____4841 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___155_4905 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_4905.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_4905.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___155_4905.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___155_4905.FStar_Syntax_Syntax.lbpos)
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
                             (let uu___156_5043 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___156_5043.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___156_5043.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___157_5044 = lb  in
                      let uu____5045 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___157_5044.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___157_5044.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5045;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___157_5044.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___157_5044.FStar_Syntax_Syntax.lbpos)
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
                      let uu___158_5286 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___158_5286.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___158_5286.FStar_Syntax_Syntax.vars)
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
                                ((let uu___159_5872 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___159_5872.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___160_5891 = x  in
                             let uu____5892 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_5891.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_5891.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5892
                             }  in
                           ((let uu___161_5906 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___161_5906.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___162_5917 = x  in
                             let uu____5918 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_5917.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_5917.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5918
                             }  in
                           ((let uu___163_5932 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___163_5932.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___164_5948 = x  in
                             let uu____5949 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___164_5948.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___164_5948.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5949
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___165_5966 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___165_5966.FStar_Syntax_Syntax.p)
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
                          let uu___166_6560 = b  in
                          let uu____6561 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_6560.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_6560.FStar_Syntax_Syntax.index);
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
                        (fun uu___108_6778  ->
                           match uu___108_6778 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6782 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6782
                           | f -> f))
                    in
                 let uu____6786 =
                   let uu___167_6787 = c1  in
                   let uu____6788 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6788;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_6787.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___109_6798  ->
            match uu___109_6798 with
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
                   (fun uu___110_6820  ->
                      match uu___110_6820 with
                      | FStar_Syntax_Syntax.DECREASES uu____6821 -> false
                      | uu____6824 -> true))
               in
            let rc1 =
              let uu___168_6826 = rc  in
              let uu____6827 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_6826.FStar_Syntax_Syntax.residual_effect);
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
    let uu____7733 =
      let uu____7736 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7736  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7733  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7778 =
      let uu____7779 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7779  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7778
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7843 = arg_as_string a1  in
        (match uu____7843 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7849 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7849 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7862 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7862
              | uu____7863 -> FStar_Pervasives_Native.None)
         | uu____7868 -> FStar_Pervasives_Native.None)
    | uu____7871 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7891 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7891
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7928 =
          let uu____7949 = arg_as_string fn  in
          let uu____7952 = arg_as_int from_line  in
          let uu____7955 = arg_as_int from_col  in
          let uu____7958 = arg_as_int to_line  in
          let uu____7961 = arg_as_int to_col  in
          (uu____7949, uu____7952, uu____7955, uu____7958, uu____7961)  in
        (match uu____7928 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7992 =
                 let uu____7993 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7994 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7993 uu____7994  in
               let uu____7995 =
                 let uu____7996 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7997 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7996 uu____7997  in
               FStar_Range.mk_range fn1 uu____7992 uu____7995  in
             let uu____7998 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7998
         | uu____7999 -> FStar_Pervasives_Native.None)
    | uu____8020 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8053)::(a1,uu____8055)::(a2,uu____8057)::[] ->
        let uu____8094 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8094 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8099 -> FStar_Pervasives_Native.None)
    | uu____8100 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8131)::[] ->
        let uu____8140 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8140 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8146 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8146
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8147 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8173 =
      let uu____8190 =
        let uu____8207 =
          let uu____8224 =
            let uu____8241 =
              let uu____8258 =
                let uu____8275 =
                  let uu____8292 =
                    let uu____8309 =
                      let uu____8326 =
                        let uu____8343 =
                          let uu____8360 =
                            let uu____8377 =
                              let uu____8394 =
                                let uu____8411 =
                                  let uu____8428 =
                                    let uu____8445 =
                                      let uu____8462 =
                                        let uu____8479 =
                                          let uu____8496 =
                                            let uu____8513 =
                                              let uu____8530 =
                                                let uu____8545 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8545,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8554 =
                                                let uu____8571 =
                                                  let uu____8586 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8586,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8599 =
                                                  let uu____8616 =
                                                    let uu____8631 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8631,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8640 =
                                                    let uu____8657 =
                                                      let uu____8672 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8672,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8657]  in
                                                  uu____8616 :: uu____8640
                                                   in
                                                uu____8571 :: uu____8599  in
                                              uu____8530 :: uu____8554  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8513
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8496
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8479
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8462
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8445
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8892 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8892 y)))
                                    :: uu____8428
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8411
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8394
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8377
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8360
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8343
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8326
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9087 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9087)))
                      :: uu____8309
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9117 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9117)))
                    :: uu____8292
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9147 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9147)))
                  :: uu____8275
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9177 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9177)))
                :: uu____8258
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8241
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8224
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8207
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8190
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8173
     in
  let weak_ops =
    let uu____9332 =
      let uu____9347 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9347, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9332]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9427 =
        let uu____9432 =
          let uu____9433 = FStar_Syntax_Syntax.as_arg c  in [uu____9433]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9432  in
      uu____9427 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9507 =
                let uu____9522 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9522, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9544  ->
                          fun uu____9545  ->
                            match (uu____9544, uu____9545) with
                            | ((int_to_t1,x),(uu____9564,y)) ->
                                let uu____9574 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9574)))
                 in
              let uu____9575 =
                let uu____9592 =
                  let uu____9607 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9607, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9629  ->
                            fun uu____9630  ->
                              match (uu____9629, uu____9630) with
                              | ((int_to_t1,x),(uu____9649,y)) ->
                                  let uu____9659 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9659)))
                   in
                let uu____9660 =
                  let uu____9677 =
                    let uu____9692 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9692, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9714  ->
                              fun uu____9715  ->
                                match (uu____9714, uu____9715) with
                                | ((int_to_t1,x),(uu____9734,y)) ->
                                    let uu____9744 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9744)))
                     in
                  let uu____9745 =
                    let uu____9762 =
                      let uu____9777 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9777, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9795  ->
                                match uu____9795 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9762]  in
                  uu____9677 :: uu____9745  in
                uu____9592 :: uu____9660  in
              uu____9507 :: uu____9575))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9925 =
                let uu____9940 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9940, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9962  ->
                          fun uu____9963  ->
                            match (uu____9962, uu____9963) with
                            | ((int_to_t1,x),(uu____9982,y)) ->
                                let uu____9992 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9992)))
                 in
              let uu____9993 =
                let uu____10010 =
                  let uu____10025 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10025, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10047  ->
                            fun uu____10048  ->
                              match (uu____10047, uu____10048) with
                              | ((int_to_t1,x),(uu____10067,y)) ->
                                  let uu____10077 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10077)))
                   in
                [uu____10010]  in
              uu____9925 :: uu____9993))
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
    | (_typ,uu____10207)::(a1,uu____10209)::(a2,uu____10211)::[] ->
        let uu____10248 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10248 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10252 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10252.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10252.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10254 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10254.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10254.FStar_Syntax_Syntax.vars)
                })
         | uu____10255 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10257)::uu____10258::(a1,uu____10260)::(a2,uu____10262)::[]
        ->
        let uu____10311 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10311 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10315 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10315.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10315.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10317 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10317.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10317.FStar_Syntax_Syntax.vars)
                })
         | uu____10318 -> FStar_Pervasives_Native.None)
    | uu____10319 -> failwith "Unexpected number of arguments"  in
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
    let uu____10373 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10373 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10425 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10425) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10487  ->
           fun subst1  ->
             match uu____10487 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10528,uu____10529)) ->
                      let uu____10588 = b  in
                      (match uu____10588 with
                       | (bv,uu____10596) ->
                           let uu____10597 =
                             let uu____10598 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10598  in
                           if uu____10597
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10603 = unembed_binder term1  in
                              match uu____10603 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10610 =
                                      let uu___171_10611 = bv  in
                                      let uu____10612 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___171_10611.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___171_10611.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10612
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10610
                                     in
                                  let b_for_x =
                                    let uu____10616 =
                                      let uu____10623 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10623)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10616  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___111_10637  ->
                                         match uu___111_10637 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10638,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10640;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10641;_})
                                             ->
                                             let uu____10646 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10646
                                         | uu____10647 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10648 -> subst1)) env []
  
let reduce_primops :
  'Auu____10671 'Auu____10672 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10671) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10672 ->
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
            (let uu____10720 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10720 with
             | (head1,args) ->
                 let uu____10759 =
                   let uu____10760 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10760.FStar_Syntax_Syntax.n  in
                 (match uu____10759 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10766 = find_prim_step cfg fv  in
                      (match uu____10766 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10792  ->
                                   let uu____10793 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10794 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10801 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10793 uu____10794 uu____10801);
                              tm)
                           else
                             (let uu____10803 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10803 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10916  ->
                                        let uu____10917 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10917);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10920  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10922 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10922 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10930  ->
                                              let uu____10931 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10931);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10937  ->
                                              let uu____10938 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10939 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10938 uu____10939);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10940 ->
                           (log_primops cfg
                              (fun uu____10944  ->
                                 let uu____10945 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10945);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10949  ->
                            let uu____10950 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10950);
                       (match args with
                        | (a1,uu____10954)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10971 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10983  ->
                            let uu____10984 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10984);
                       (match args with
                        | (t,uu____10988)::(r,uu____10990)::[] ->
                            let uu____11017 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11017 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11023 -> tm))
                  | uu____11032 -> tm))
  
let reduce_equality :
  'Auu____11043 'Auu____11044 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11043) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11044 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___172_11090 = cfg  in
         {
           steps =
             (let uu___173_11093 = default_steps  in
              {
                beta = (uu___173_11093.beta);
                iota = (uu___173_11093.iota);
                zeta = (uu___173_11093.zeta);
                weak = (uu___173_11093.weak);
                hnf = (uu___173_11093.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___173_11093.do_not_unfold_pure_lets);
                unfold_until = (uu___173_11093.unfold_until);
                unfold_only = (uu___173_11093.unfold_only);
                unfold_fully = (uu___173_11093.unfold_fully);
                unfold_attr = (uu___173_11093.unfold_attr);
                unfold_tac = (uu___173_11093.unfold_tac);
                pure_subterms_within_computations =
                  (uu___173_11093.pure_subterms_within_computations);
                simplify = (uu___173_11093.simplify);
                erase_universes = (uu___173_11093.erase_universes);
                allow_unbound_universes =
                  (uu___173_11093.allow_unbound_universes);
                reify_ = (uu___173_11093.reify_);
                compress_uvars = (uu___173_11093.compress_uvars);
                no_full_norm = (uu___173_11093.no_full_norm);
                check_no_uvars = (uu___173_11093.check_no_uvars);
                unmeta = (uu___173_11093.unmeta);
                unascribe = (uu___173_11093.unascribe);
                in_full_norm_request = (uu___173_11093.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___173_11093.weakly_reduce_scrutinee)
              });
           tcenv = (uu___172_11090.tcenv);
           debug = (uu___172_11090.debug);
           delta_level = (uu___172_11090.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___172_11090.strong);
           memoize_lazy = (uu___172_11090.memoize_lazy);
           normalize_pure_lets = (uu___172_11090.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11100 .
    FStar_Syntax_Syntax.term -> 'Auu____11100 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11115 =
        let uu____11122 =
          let uu____11123 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11123.FStar_Syntax_Syntax.n  in
        (uu____11122, args)  in
      match uu____11115 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11129::uu____11130::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11134::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11139::uu____11140::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11143 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___112_11156  ->
    match uu___112_11156 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11162 =
          let uu____11165 =
            let uu____11166 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11166  in
          [uu____11165]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11162
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11172 =
          let uu____11175 =
            let uu____11176 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11176  in
          [uu____11175]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11172
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11199 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11199)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11250 =
            let uu____11255 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11255 s  in
          match uu____11250 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11271 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11271
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11297::(tm,uu____11299)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11328)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11349)::uu____11350::(tm,uu____11352)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11393 =
              let uu____11398 = full_norm steps  in parse_steps uu____11398
               in
            (match uu____11393 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11437 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___113_11456  ->
    match uu___113_11456 with
    | (App
        (uu____11459,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11460;
                       FStar_Syntax_Syntax.vars = uu____11461;_},uu____11462,uu____11463))::uu____11464
        -> true
    | uu____11469 -> false
  
let firstn :
  'Auu____11478 .
    Prims.int ->
      'Auu____11478 Prims.list ->
        ('Auu____11478 Prims.list,'Auu____11478 Prims.list)
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
          (uu____11520,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11521;
                         FStar_Syntax_Syntax.vars = uu____11522;_},uu____11523,uu____11524))::uu____11525
          -> (cfg.steps).reify_
      | uu____11530 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11553) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11563) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11582  ->
                  match uu____11582 with
                  | (a,uu____11590) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11596 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11621 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11622 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11637 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11638 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11639 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11640 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11641 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11642 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11649 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11656 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11669 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11686 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11699 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11706 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11768  ->
                   match uu____11768 with
                   | (a,uu____11776) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11783) ->
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
                     (fun uu____11905  ->
                        match uu____11905 with
                        | (a,uu____11913) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11918,uu____11919,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11925,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11931 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11938 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11939 -> false))
  
let decide_unfolding :
  'Auu____11954 .
    cfg ->
      'Auu____11954 ->
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
                let uu____12040 =
                  FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                match uu____12040 with
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
                  (fun uu____12168  ->
                     fun uu____12169  ->
                       match (uu____12168, uu____12169) with
                       | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                  l (false, false, false)
                 in
              let string_of_res uu____12229 =
                match uu____12229 with
                | (x,y,z) ->
                    let uu____12239 = FStar_Util.string_of_bool x  in
                    let uu____12240 = FStar_Util.string_of_bool y  in
                    let uu____12241 = FStar_Util.string_of_bool z  in
                    FStar_Util.format3 "(%s,%s,%s)" uu____12239 uu____12240
                      uu____12241
                 in
              let res =
                match (qninfo, ((cfg.steps).unfold_only),
                        ((cfg.steps).unfold_fully),
                        ((cfg.steps).unfold_attr))
                with
                | uu____12287 when
                    FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                    let b = should_reify cfg stack  in
                    (log_unfolding cfg
                       (fun uu____12333  ->
                          let uu____12334 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          let uu____12335 = FStar_Util.string_of_bool b  in
                          FStar_Util.print2
                            ">>> For DM4F action %s, should_reify = %s\n"
                            uu____12334 uu____12335);
                     if b then reif else no)
                | uu____12343 when
                    let uu____12384 = find_prim_step cfg fv  in
                    FStar_Option.isSome uu____12384 -> no
                | (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr
                    ({
                       FStar_Syntax_Syntax.sigel =
                         FStar_Syntax_Syntax.Sig_let
                         ((is_rec,uu____12388),uu____12389);
                       FStar_Syntax_Syntax.sigrng = uu____12390;
                       FStar_Syntax_Syntax.sigquals = qs;
                       FStar_Syntax_Syntax.sigmeta = uu____12392;
                       FStar_Syntax_Syntax.sigattrs = uu____12393;_},uu____12394),uu____12395),uu____12396,uu____12397,uu____12398)
                    when
                    FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                      qs
                    -> no
                | (uu____12501,uu____12502,uu____12503,uu____12504) when
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
                         ((is_rec,uu____12570),uu____12571);
                       FStar_Syntax_Syntax.sigrng = uu____12572;
                       FStar_Syntax_Syntax.sigquals = qs;
                       FStar_Syntax_Syntax.sigmeta = uu____12574;
                       FStar_Syntax_Syntax.sigattrs = uu____12575;_},uu____12576),uu____12577),uu____12578,uu____12579,uu____12580)
                    when is_rec && (Prims.op_Negation (cfg.steps).zeta) -> no
                | (uu____12683,FStar_Pervasives_Native.Some
                   uu____12684,uu____12685,uu____12686) ->
                    (log_unfolding cfg
                       (fun uu____12754  ->
                          let uu____12755 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____12755);
                     (let uu____12756 =
                        let uu____12765 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12785 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____12785
                           in
                        let uu____12792 =
                          let uu____12801 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____12821 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____12821
                             in
                          let uu____12830 =
                            let uu____12839 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____12859 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____12859
                               in
                            [uu____12839]  in
                          uu____12801 :: uu____12830  in
                        uu____12765 :: uu____12792  in
                      comb_or uu____12756))
                | (uu____12890,uu____12891,FStar_Pervasives_Native.Some
                   uu____12892,uu____12893) ->
                    (log_unfolding cfg
                       (fun uu____12961  ->
                          let uu____12962 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____12962);
                     (let uu____12963 =
                        let uu____12972 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____12992 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____12992
                           in
                        let uu____12999 =
                          let uu____13008 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____13028 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____13028
                             in
                          let uu____13037 =
                            let uu____13046 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____13066 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____13066
                               in
                            [uu____13046]  in
                          uu____13008 :: uu____13037  in
                        uu____12972 :: uu____12999  in
                      comb_or uu____12963))
                | (uu____13097,uu____13098,uu____13099,FStar_Pervasives_Native.Some
                   uu____13100) ->
                    (log_unfolding cfg
                       (fun uu____13168  ->
                          let uu____13169 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          FStar_Util.print1
                            ">>> Reached a %s with selective unfolding\n"
                            uu____13169);
                     (let uu____13170 =
                        let uu____13179 =
                          match (cfg.steps).unfold_only with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____13199 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left yesno uu____13199
                           in
                        let uu____13206 =
                          let uu____13215 =
                            match (cfg.steps).unfold_attr with
                            | FStar_Pervasives_Native.None  -> no
                            | FStar_Pervasives_Native.Some ats ->
                                let uu____13235 =
                                  FStar_Util.for_some
                                    (fun at  ->
                                       FStar_Util.for_some
                                         (FStar_Syntax_Util.attr_eq at) ats)
                                    attrs
                                   in
                                FStar_All.pipe_left yesno uu____13235
                             in
                          let uu____13244 =
                            let uu____13253 =
                              match (cfg.steps).unfold_fully with
                              | FStar_Pervasives_Native.None  -> no
                              | FStar_Pervasives_Native.Some lids ->
                                  let uu____13273 =
                                    FStar_Util.for_some
                                      (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                     in
                                  FStar_All.pipe_left fullyno uu____13273
                               in
                            [uu____13253]  in
                          uu____13215 :: uu____13244  in
                        uu____13179 :: uu____13206  in
                      comb_or uu____13170))
                | uu____13304 ->
                    (log_unfolding cfg
                       (fun uu____13350  ->
                          let uu____13351 =
                            FStar_Syntax_Print.fv_to_string fv  in
                          let uu____13352 =
                            FStar_Syntax_Print.delta_depth_to_string
                              fv.FStar_Syntax_Syntax.fv_delta
                             in
                          let uu____13353 =
                            FStar_Common.string_of_list
                              FStar_TypeChecker_Env.string_of_delta_level
                              cfg.delta_level
                             in
                          FStar_Util.print3
                            ">>> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                            uu____13351 uu____13352 uu____13353);
                     (let uu____13354 =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_Util.for_some
                             (fun uu___114_13358  ->
                                match uu___114_13358 with
                                | FStar_TypeChecker_Env.UnfoldTac  -> false
                                | FStar_TypeChecker_Env.NoDelta  -> false
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | FStar_TypeChecker_Env.Unfold l ->
                                    FStar_TypeChecker_Common.delta_depth_greater_than
                                      fv.FStar_Syntax_Syntax.fv_delta l))
                         in
                      FStar_All.pipe_left yesno uu____13354))
                 in
              log_unfolding cfg
                (fun uu____13371  ->
                   let uu____13372 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____13373 = FStar_Range.string_of_range rng  in
                   let uu____13374 = string_of_res res  in
                   FStar_Util.print3 ">>> For %s (%s), unfolding res = %s\n"
                     uu____13372 uu____13373 uu____13374);
              (match res with
               | (false ,uu____13383,uu____13384) ->
                   FStar_Pervasives_Native.None
               | (true ,false ,false ) ->
                   FStar_Pervasives_Native.Some (cfg, stack)
               | (true ,true ,false ) ->
                   let cfg' =
                     let uu___174_13400 = cfg  in
                     {
                       steps =
                         (let uu___175_13403 = cfg.steps  in
                          {
                            beta = (uu___175_13403.beta);
                            iota = false;
                            zeta = false;
                            weak = false;
                            hnf = false;
                            primops = false;
                            do_not_unfold_pure_lets =
                              (uu___175_13403.do_not_unfold_pure_lets);
                            unfold_until =
                              (FStar_Pervasives_Native.Some
                                 FStar_Syntax_Syntax.delta_constant);
                            unfold_only = FStar_Pervasives_Native.None;
                            unfold_fully = FStar_Pervasives_Native.None;
                            unfold_attr = (uu___175_13403.unfold_attr);
                            unfold_tac = (uu___175_13403.unfold_tac);
                            pure_subterms_within_computations =
                              (uu___175_13403.pure_subterms_within_computations);
                            simplify = false;
                            erase_universes =
                              (uu___175_13403.erase_universes);
                            allow_unbound_universes =
                              (uu___175_13403.allow_unbound_universes);
                            reify_ = (uu___175_13403.reify_);
                            compress_uvars = (uu___175_13403.compress_uvars);
                            no_full_norm = (uu___175_13403.no_full_norm);
                            check_no_uvars = (uu___175_13403.check_no_uvars);
                            unmeta = (uu___175_13403.unmeta);
                            unascribe = (uu___175_13403.unascribe);
                            in_full_norm_request =
                              (uu___175_13403.in_full_norm_request);
                            weakly_reduce_scrutinee =
                              (uu___175_13403.weakly_reduce_scrutinee)
                          });
                       tcenv = (uu___174_13400.tcenv);
                       debug = (uu___174_13400.debug);
                       delta_level = (uu___174_13400.delta_level);
                       primitive_steps = (uu___174_13400.primitive_steps);
                       strong = (uu___174_13400.strong);
                       memoize_lazy = (uu___174_13400.memoize_lazy);
                       normalize_pure_lets =
                         (uu___174_13400.normalize_pure_lets)
                     }  in
                   let stack' = (Cfg cfg) :: stack  in
                   FStar_Pervasives_Native.Some (cfg', stack')
               | (true ,false ,true ) ->
                   let uu____13419 =
                     let uu____13426 = FStar_List.tl stack  in
                     (cfg, uu____13426)  in
                   FStar_Pervasives_Native.Some uu____13419
               | uu____13437 ->
                   let uu____13444 =
                     let uu____13445 = string_of_res res  in
                     FStar_Util.format1 "Unexpected unfolding result: %s"
                       uu____13445
                      in
                   FStar_All.pipe_left failwith uu____13444)
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13753 ->
                   let uu____13778 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13778
               | uu____13779 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13787  ->
               let uu____13788 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13789 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13790 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13797 =
                 let uu____13798 =
                   let uu____13801 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13801
                    in
                 stack_to_string uu____13798  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13788 uu____13789 uu____13790 uu____13797);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13824 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13825 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13826 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13827;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____13828;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13831;
                 FStar_Syntax_Syntax.fv_delta = uu____13832;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13833;
                 FStar_Syntax_Syntax.fv_delta = uu____13834;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13835);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____13842 ->
               let uu____13849 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13849
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____13879 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____13879)
               ->
               let cfg' =
                 let uu___176_13881 = cfg  in
                 {
                   steps =
                     (let uu___177_13884 = cfg.steps  in
                      {
                        beta = (uu___177_13884.beta);
                        iota = (uu___177_13884.iota);
                        zeta = (uu___177_13884.zeta);
                        weak = (uu___177_13884.weak);
                        hnf = (uu___177_13884.hnf);
                        primops = (uu___177_13884.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___177_13884.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___177_13884.unfold_attr);
                        unfold_tac = (uu___177_13884.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___177_13884.pure_subterms_within_computations);
                        simplify = (uu___177_13884.simplify);
                        erase_universes = (uu___177_13884.erase_universes);
                        allow_unbound_universes =
                          (uu___177_13884.allow_unbound_universes);
                        reify_ = (uu___177_13884.reify_);
                        compress_uvars = (uu___177_13884.compress_uvars);
                        no_full_norm = (uu___177_13884.no_full_norm);
                        check_no_uvars = (uu___177_13884.check_no_uvars);
                        unmeta = (uu___177_13884.unmeta);
                        unascribe = (uu___177_13884.unascribe);
                        in_full_norm_request =
                          (uu___177_13884.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___177_13884.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___176_13881.tcenv);
                   debug = (uu___176_13881.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___176_13881.primitive_steps);
                   strong = (uu___176_13881.strong);
                   memoize_lazy = (uu___176_13881.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13889 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____13889 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____13918  ->
                              fun stack1  ->
                                match uu____13918 with
                                | (a,aq) ->
                                    let uu____13930 =
                                      let uu____13931 =
                                        let uu____13938 =
                                          let uu____13939 =
                                            let uu____13970 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____13970, false)  in
                                          Clos uu____13939  in
                                        (uu____13938, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____13931  in
                                    uu____13930 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14058  ->
                          let uu____14059 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14059);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14081 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___115_14086  ->
                                match uu___115_14086 with
                                | UnfoldUntil uu____14087 -> true
                                | UnfoldOnly uu____14088 -> true
                                | UnfoldFully uu____14091 -> true
                                | uu____14094 -> false))
                         in
                      if uu____14081
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___178_14099 = cfg  in
                      let uu____14100 =
                        let uu___179_14101 = to_fsteps s  in
                        {
                          beta = (uu___179_14101.beta);
                          iota = (uu___179_14101.iota);
                          zeta = (uu___179_14101.zeta);
                          weak = (uu___179_14101.weak);
                          hnf = (uu___179_14101.hnf);
                          primops = (uu___179_14101.primops);
                          do_not_unfold_pure_lets =
                            (uu___179_14101.do_not_unfold_pure_lets);
                          unfold_until = (uu___179_14101.unfold_until);
                          unfold_only = (uu___179_14101.unfold_only);
                          unfold_fully = (uu___179_14101.unfold_fully);
                          unfold_attr = (uu___179_14101.unfold_attr);
                          unfold_tac = (uu___179_14101.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___179_14101.pure_subterms_within_computations);
                          simplify = (uu___179_14101.simplify);
                          erase_universes = (uu___179_14101.erase_universes);
                          allow_unbound_universes =
                            (uu___179_14101.allow_unbound_universes);
                          reify_ = (uu___179_14101.reify_);
                          compress_uvars = (uu___179_14101.compress_uvars);
                          no_full_norm = (uu___179_14101.no_full_norm);
                          check_no_uvars = (uu___179_14101.check_no_uvars);
                          unmeta = (uu___179_14101.unmeta);
                          unascribe = (uu___179_14101.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___179_14101.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14100;
                        tcenv = (uu___178_14099.tcenv);
                        debug = (uu___178_14099.debug);
                        delta_level;
                        primitive_steps = (uu___178_14099.primitive_steps);
                        strong = (uu___178_14099.strong);
                        memoize_lazy = (uu___178_14099.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14106 =
                          let uu____14107 =
                            let uu____14112 = FStar_Util.now ()  in
                            (t1, uu____14112)  in
                          Debug uu____14107  in
                        uu____14106 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14116 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14116
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14125 =
                      let uu____14132 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14132, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14125  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14142 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14142  in
               let uu____14143 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14143 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14171 = lookup_bvar env x  in
               (match uu____14171 with
                | Univ uu____14172 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14221 = FStar_ST.op_Bang r  in
                      (match uu____14221 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14343  ->
                                 let uu____14344 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14345 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14344
                                   uu____14345);
                            (let uu____14346 = maybe_weakly_reduced t'  in
                             if uu____14346
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14347 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14418)::uu____14419 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14429,uu____14430))::stack_rest ->
                    (match c with
                     | Univ uu____14434 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14443 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14464  ->
                                    let uu____14465 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14465);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14493  ->
                                    let uu____14494 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14494);
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
                       (fun uu____14560  ->
                          let uu____14561 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14561);
                     norm cfg env stack1 t1)
                | (Match uu____14562)::uu____14563 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14577 = cfg.steps  in
                             {
                               beta = (uu___180_14577.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14577.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14577.unfold_until);
                               unfold_only = (uu___180_14577.unfold_only);
                               unfold_fully = (uu___180_14577.unfold_fully);
                               unfold_attr = (uu___180_14577.unfold_attr);
                               unfold_tac = (uu___180_14577.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14577.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14577.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14577.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14577.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14577.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14577.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14579 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14579.tcenv);
                               debug = (uu___181_14579.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14579.primitive_steps);
                               strong = (uu___181_14579.strong);
                               memoize_lazy = (uu___181_14579.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14579.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14581 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14581 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14613  -> dummy :: env1) env)
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
                                          let uu____14654 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14654)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14661 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14661.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14661.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14662 -> lopt  in
                           (log cfg
                              (fun uu____14668  ->
                                 let uu____14669 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14669);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14678 = cfg  in
                               {
                                 steps = (uu___183_14678.steps);
                                 tcenv = (uu___183_14678.tcenv);
                                 debug = (uu___183_14678.debug);
                                 delta_level = (uu___183_14678.delta_level);
                                 primitive_steps =
                                   (uu___183_14678.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14678.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14678.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____14681)::uu____14682 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14692 = cfg.steps  in
                             {
                               beta = (uu___180_14692.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14692.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14692.unfold_until);
                               unfold_only = (uu___180_14692.unfold_only);
                               unfold_fully = (uu___180_14692.unfold_fully);
                               unfold_attr = (uu___180_14692.unfold_attr);
                               unfold_tac = (uu___180_14692.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14692.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14692.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14692.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14692.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14692.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14692.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14694 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14694.tcenv);
                               debug = (uu___181_14694.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14694.primitive_steps);
                               strong = (uu___181_14694.strong);
                               memoize_lazy = (uu___181_14694.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14694.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14696 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14696 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14728  -> dummy :: env1) env)
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
                                          let uu____14769 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14769)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14776 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14776.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14776.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14777 -> lopt  in
                           (log cfg
                              (fun uu____14783  ->
                                 let uu____14784 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14784);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14793 = cfg  in
                               {
                                 steps = (uu___183_14793.steps);
                                 tcenv = (uu___183_14793.tcenv);
                                 debug = (uu___183_14793.debug);
                                 delta_level = (uu___183_14793.delta_level);
                                 primitive_steps =
                                   (uu___183_14793.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14793.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14793.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14796)::uu____14797 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14809 = cfg.steps  in
                             {
                               beta = (uu___180_14809.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14809.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14809.unfold_until);
                               unfold_only = (uu___180_14809.unfold_only);
                               unfold_fully = (uu___180_14809.unfold_fully);
                               unfold_attr = (uu___180_14809.unfold_attr);
                               unfold_tac = (uu___180_14809.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14809.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14809.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14809.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14809.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14809.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14809.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14811 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14811.tcenv);
                               debug = (uu___181_14811.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14811.primitive_steps);
                               strong = (uu___181_14811.strong);
                               memoize_lazy = (uu___181_14811.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14811.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14813 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14813 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14845  -> dummy :: env1) env)
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
                                          let uu____14886 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14886)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_14893 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_14893.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_14893.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14894 -> lopt  in
                           (log cfg
                              (fun uu____14900  ->
                                 let uu____14901 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14901);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_14910 = cfg  in
                               {
                                 steps = (uu___183_14910.steps);
                                 tcenv = (uu___183_14910.tcenv);
                                 debug = (uu___183_14910.debug);
                                 delta_level = (uu___183_14910.delta_level);
                                 primitive_steps =
                                   (uu___183_14910.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_14910.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14910.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14913)::uu____14914 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_14928 = cfg.steps  in
                             {
                               beta = (uu___180_14928.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_14928.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_14928.unfold_until);
                               unfold_only = (uu___180_14928.unfold_only);
                               unfold_fully = (uu___180_14928.unfold_fully);
                               unfold_attr = (uu___180_14928.unfold_attr);
                               unfold_tac = (uu___180_14928.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_14928.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_14928.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_14928.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_14928.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_14928.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_14928.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_14930 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_14930.tcenv);
                               debug = (uu___181_14930.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_14930.primitive_steps);
                               strong = (uu___181_14930.strong);
                               memoize_lazy = (uu___181_14930.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_14930.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14932 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14932 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14964  -> dummy :: env1) env)
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
                                          let uu____15005 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15005)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15012 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15012.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15012.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15013 -> lopt  in
                           (log cfg
                              (fun uu____15019  ->
                                 let uu____15020 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15020);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15029 = cfg  in
                               {
                                 steps = (uu___183_15029.steps);
                                 tcenv = (uu___183_15029.tcenv);
                                 debug = (uu___183_15029.debug);
                                 delta_level = (uu___183_15029.delta_level);
                                 primitive_steps =
                                   (uu___183_15029.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15029.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15029.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15032)::uu____15033 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_15047 = cfg.steps  in
                             {
                               beta = (uu___180_15047.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_15047.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_15047.unfold_until);
                               unfold_only = (uu___180_15047.unfold_only);
                               unfold_fully = (uu___180_15047.unfold_fully);
                               unfold_attr = (uu___180_15047.unfold_attr);
                               unfold_tac = (uu___180_15047.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_15047.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_15047.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_15047.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_15047.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_15047.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_15047.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_15049 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_15049.tcenv);
                               debug = (uu___181_15049.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_15049.primitive_steps);
                               strong = (uu___181_15049.strong);
                               memoize_lazy = (uu___181_15049.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_15049.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15051 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15051 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15083  -> dummy :: env1) env)
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
                                          let uu____15124 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15124)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15131 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15131.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15131.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15132 -> lopt  in
                           (log cfg
                              (fun uu____15138  ->
                                 let uu____15139 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15139);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15148 = cfg  in
                               {
                                 steps = (uu___183_15148.steps);
                                 tcenv = (uu___183_15148.tcenv);
                                 debug = (uu___183_15148.debug);
                                 delta_level = (uu___183_15148.delta_level);
                                 primitive_steps =
                                   (uu___183_15148.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15148.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15148.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15151)::uu____15152 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___180_15170 = cfg.steps  in
                             {
                               beta = (uu___180_15170.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_15170.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_15170.unfold_until);
                               unfold_only = (uu___180_15170.unfold_only);
                               unfold_fully = (uu___180_15170.unfold_fully);
                               unfold_attr = (uu___180_15170.unfold_attr);
                               unfold_tac = (uu___180_15170.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_15170.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_15170.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_15170.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_15170.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_15170.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_15170.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_15172 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_15172.tcenv);
                               debug = (uu___181_15172.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_15172.primitive_steps);
                               strong = (uu___181_15172.strong);
                               memoize_lazy = (uu___181_15172.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_15172.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15174 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15174 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15206  -> dummy :: env1) env)
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
                                          let uu____15247 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15247)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15254 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15254.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15254.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15255 -> lopt  in
                           (log cfg
                              (fun uu____15261  ->
                                 let uu____15262 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15262);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15271 = cfg  in
                               {
                                 steps = (uu___183_15271.steps);
                                 tcenv = (uu___183_15271.tcenv);
                                 debug = (uu___183_15271.debug);
                                 delta_level = (uu___183_15271.delta_level);
                                 primitive_steps =
                                   (uu___183_15271.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15271.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15271.normalize_pure_lets)
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
                             let uu___180_15277 = cfg.steps  in
                             {
                               beta = (uu___180_15277.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___180_15277.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___180_15277.unfold_until);
                               unfold_only = (uu___180_15277.unfold_only);
                               unfold_fully = (uu___180_15277.unfold_fully);
                               unfold_attr = (uu___180_15277.unfold_attr);
                               unfold_tac = (uu___180_15277.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___180_15277.erase_universes);
                               allow_unbound_universes =
                                 (uu___180_15277.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___180_15277.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___180_15277.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___180_15277.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___180_15277.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___181_15279 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___181_15279.tcenv);
                               debug = (uu___181_15279.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___181_15279.primitive_steps);
                               strong = (uu___181_15279.strong);
                               memoize_lazy = (uu___181_15279.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___181_15279.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15281 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15281 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15313  -> dummy :: env1) env)
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
                                          let uu____15354 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15354)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___182_15361 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___182_15361.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___182_15361.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15362 -> lopt  in
                           (log cfg
                              (fun uu____15368  ->
                                 let uu____15369 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15369);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___183_15378 = cfg  in
                               {
                                 steps = (uu___183_15378.steps);
                                 tcenv = (uu___183_15378.tcenv);
                                 debug = (uu___183_15378.debug);
                                 delta_level = (uu___183_15378.delta_level);
                                 primitive_steps =
                                   (uu___183_15378.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___183_15378.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_15378.normalize_pure_lets)
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
                      (fun uu____15417  ->
                         fun stack1  ->
                           match uu____15417 with
                           | (a,aq) ->
                               let uu____15429 =
                                 let uu____15430 =
                                   let uu____15437 =
                                     let uu____15438 =
                                       let uu____15469 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15469, false)  in
                                     Clos uu____15438  in
                                   (uu____15437, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15430  in
                               uu____15429 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15557  ->
                     let uu____15558 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15558);
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
                             ((let uu___184_15604 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___184_15604.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___184_15604.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15605 ->
                      let uu____15620 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15620)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15623 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15623 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15648 =
                          let uu____15649 =
                            let uu____15656 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___185_15662 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___185_15662.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___185_15662.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15656)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15649  in
                        mk uu____15648 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15681 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15681
               else
                 (let uu____15683 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15683 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15691 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15713  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15691 c1  in
                      let t2 =
                        let uu____15735 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15735 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15846)::uu____15847 ->
                    (log cfg
                       (fun uu____15860  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15861)::uu____15862 ->
                    (log cfg
                       (fun uu____15873  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15874,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15875;
                                   FStar_Syntax_Syntax.vars = uu____15876;_},uu____15877,uu____15878))::uu____15879
                    ->
                    (log cfg
                       (fun uu____15886  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15887)::uu____15888 ->
                    (log cfg
                       (fun uu____15899  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15900 ->
                    (log cfg
                       (fun uu____15903  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15907  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15932 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15932
                         | FStar_Util.Inr c ->
                             let uu____15946 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____15946
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____15969 =
                               let uu____15970 =
                                 let uu____15997 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____15997, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15970
                                in
                             mk uu____15969 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16032 ->
                           let uu____16033 =
                             let uu____16034 =
                               let uu____16035 =
                                 let uu____16062 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16062, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16035
                                in
                             mk uu____16034 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16033))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___186_16139 = cfg  in
                   {
                     steps =
                       (let uu___187_16142 = cfg.steps  in
                        {
                          beta = (uu___187_16142.beta);
                          iota = (uu___187_16142.iota);
                          zeta = (uu___187_16142.zeta);
                          weak = true;
                          hnf = (uu___187_16142.hnf);
                          primops = (uu___187_16142.primops);
                          do_not_unfold_pure_lets =
                            (uu___187_16142.do_not_unfold_pure_lets);
                          unfold_until = (uu___187_16142.unfold_until);
                          unfold_only = (uu___187_16142.unfold_only);
                          unfold_fully = (uu___187_16142.unfold_fully);
                          unfold_attr = (uu___187_16142.unfold_attr);
                          unfold_tac = (uu___187_16142.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___187_16142.pure_subterms_within_computations);
                          simplify = (uu___187_16142.simplify);
                          erase_universes = (uu___187_16142.erase_universes);
                          allow_unbound_universes =
                            (uu___187_16142.allow_unbound_universes);
                          reify_ = (uu___187_16142.reify_);
                          compress_uvars = (uu___187_16142.compress_uvars);
                          no_full_norm = (uu___187_16142.no_full_norm);
                          check_no_uvars = (uu___187_16142.check_no_uvars);
                          unmeta = (uu___187_16142.unmeta);
                          unascribe = (uu___187_16142.unascribe);
                          in_full_norm_request =
                            (uu___187_16142.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___187_16142.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___186_16139.tcenv);
                     debug = (uu___186_16139.debug);
                     delta_level = (uu___186_16139.delta_level);
                     primitive_steps = (uu___186_16139.primitive_steps);
                     strong = (uu___186_16139.strong);
                     memoize_lazy = (uu___186_16139.memoize_lazy);
                     normalize_pure_lets =
                       (uu___186_16139.normalize_pure_lets)
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
                         let uu____16178 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16178 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___188_16198 = cfg  in
                               let uu____16199 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___188_16198.steps);
                                 tcenv = uu____16199;
                                 debug = (uu___188_16198.debug);
                                 delta_level = (uu___188_16198.delta_level);
                                 primitive_steps =
                                   (uu___188_16198.primitive_steps);
                                 strong = (uu___188_16198.strong);
                                 memoize_lazy = (uu___188_16198.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_16198.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16206 =
                                 let uu____16207 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16207  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16206
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___189_16210 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___189_16210.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___189_16210.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___189_16210.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___189_16210.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16211 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16211
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16222,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16223;
                               FStar_Syntax_Syntax.lbunivs = uu____16224;
                               FStar_Syntax_Syntax.lbtyp = uu____16225;
                               FStar_Syntax_Syntax.lbeff = uu____16226;
                               FStar_Syntax_Syntax.lbdef = uu____16227;
                               FStar_Syntax_Syntax.lbattrs = uu____16228;
                               FStar_Syntax_Syntax.lbpos = uu____16229;_}::uu____16230),uu____16231)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16271 =
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
               if uu____16271
               then
                 let binder =
                   let uu____16273 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16273  in
                 let env1 =
                   let uu____16283 =
                     let uu____16290 =
                       let uu____16291 =
                         let uu____16322 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16322,
                           false)
                          in
                       Clos uu____16291  in
                     ((FStar_Pervasives_Native.Some binder), uu____16290)  in
                   uu____16283 :: env  in
                 (log cfg
                    (fun uu____16417  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16421  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16422 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16422))
                 else
                   (let uu____16424 =
                      let uu____16429 =
                        let uu____16430 =
                          let uu____16435 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16435
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16430]  in
                      FStar_Syntax_Subst.open_term uu____16429 body  in
                    match uu____16424 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16456  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16464 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16464  in
                            FStar_Util.Inl
                              (let uu___190_16474 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___190_16474.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___190_16474.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16477  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___191_16479 = lb  in
                             let uu____16480 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___191_16479.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___191_16479.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16480;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___191_16479.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___191_16479.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16505  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___192_16528 = cfg  in
                             {
                               steps = (uu___192_16528.steps);
                               tcenv = (uu___192_16528.tcenv);
                               debug = (uu___192_16528.debug);
                               delta_level = (uu___192_16528.delta_level);
                               primitive_steps =
                                 (uu___192_16528.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___192_16528.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___192_16528.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16531  ->
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
               let uu____16548 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16548 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16584 =
                               let uu___193_16585 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___193_16585.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___193_16585.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16584  in
                           let uu____16586 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16586 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16612 =
                                   FStar_List.map (fun uu____16628  -> dummy)
                                     lbs1
                                    in
                                 let uu____16629 =
                                   let uu____16638 =
                                     FStar_List.map
                                       (fun uu____16658  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16638 env  in
                                 FStar_List.append uu____16612 uu____16629
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16682 =
                                       let uu___194_16683 = rc  in
                                       let uu____16684 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___194_16683.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16684;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___194_16683.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16682
                                 | uu____16693 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___195_16699 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___195_16699.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___195_16699.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___195_16699.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___195_16699.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16709 =
                        FStar_List.map (fun uu____16725  -> dummy) lbs2  in
                      FStar_List.append uu____16709 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16733 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16733 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___196_16749 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___196_16749.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___196_16749.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16778 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16778
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16797 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16873  ->
                        match uu____16873 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___197_16994 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___197_16994.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___197_16994.FStar_Syntax_Syntax.sort)
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
               (match uu____16797 with
                | (rec_env,memos,uu____17221) ->
                    let uu____17274 =
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
                             let uu____17597 =
                               let uu____17604 =
                                 let uu____17605 =
                                   let uu____17636 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17636, false)
                                    in
                                 Clos uu____17605  in
                               (FStar_Pervasives_Native.None, uu____17604)
                                in
                             uu____17597 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17740  ->
                     let uu____17741 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17741);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____17763 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17765::uu____17766 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17771) ->
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
                             | uu____17794 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17808 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17808
                              | uu____17819 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17825 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17851 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17867 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17882 =
                        let uu____17883 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17884 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17883 uu____17884
                         in
                      failwith uu____17882
                    else
                      (let uu____17886 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____17886)
                | uu____17887 -> norm cfg env stack t2))

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
                let uu____17897 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____17897  in
              let uu____17898 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17898 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____17911  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____17922  ->
                        let uu____17923 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17924 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____17923 uu____17924);
                   (let t1 =
                      if
                        (cfg.steps).unfold_until =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        (let uu____17929 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____17929 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____17938))::stack1 ->
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
                      | uu____17977 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____17980 ->
                          let uu____17983 =
                            let uu____17984 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17984
                             in
                          failwith uu____17983
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
                  let uu___198_18008 = cfg  in
                  let uu____18009 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18009;
                    tcenv = (uu___198_18008.tcenv);
                    debug = (uu___198_18008.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___198_18008.primitive_steps);
                    strong = (uu___198_18008.strong);
                    memoize_lazy = (uu___198_18008.memoize_lazy);
                    normalize_pure_lets =
                      (uu___198_18008.normalize_pure_lets)
                  }
                else
                  (let uu___199_18011 = cfg  in
                   {
                     steps =
                       (let uu___200_18014 = cfg.steps  in
                        {
                          beta = (uu___200_18014.beta);
                          iota = (uu___200_18014.iota);
                          zeta = false;
                          weak = (uu___200_18014.weak);
                          hnf = (uu___200_18014.hnf);
                          primops = (uu___200_18014.primops);
                          do_not_unfold_pure_lets =
                            (uu___200_18014.do_not_unfold_pure_lets);
                          unfold_until = (uu___200_18014.unfold_until);
                          unfold_only = (uu___200_18014.unfold_only);
                          unfold_fully = (uu___200_18014.unfold_fully);
                          unfold_attr = (uu___200_18014.unfold_attr);
                          unfold_tac = (uu___200_18014.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___200_18014.pure_subterms_within_computations);
                          simplify = (uu___200_18014.simplify);
                          erase_universes = (uu___200_18014.erase_universes);
                          allow_unbound_universes =
                            (uu___200_18014.allow_unbound_universes);
                          reify_ = (uu___200_18014.reify_);
                          compress_uvars = (uu___200_18014.compress_uvars);
                          no_full_norm = (uu___200_18014.no_full_norm);
                          check_no_uvars = (uu___200_18014.check_no_uvars);
                          unmeta = (uu___200_18014.unmeta);
                          unascribe = (uu___200_18014.unascribe);
                          in_full_norm_request =
                            (uu___200_18014.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___200_18014.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___199_18011.tcenv);
                     debug = (uu___199_18011.debug);
                     delta_level = (uu___199_18011.delta_level);
                     primitive_steps = (uu___199_18011.primitive_steps);
                     strong = (uu___199_18011.strong);
                     memoize_lazy = (uu___199_18011.memoize_lazy);
                     normalize_pure_lets =
                       (uu___199_18011.normalize_pure_lets)
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
                  (fun uu____18048  ->
                     let uu____18049 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18050 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18049
                       uu____18050);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18052 =
                   let uu____18053 = FStar_Syntax_Subst.compress head3  in
                   uu____18053.FStar_Syntax_Syntax.n  in
                 match uu____18052 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18071 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18071
                        in
                     let uu____18072 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18072 with
                      | (uu____18073,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18083 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18093 =
                                   let uu____18094 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18094.FStar_Syntax_Syntax.n  in
                                 match uu____18093 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18100,uu____18101))
                                     ->
                                     let uu____18110 =
                                       let uu____18111 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18111.FStar_Syntax_Syntax.n  in
                                     (match uu____18110 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18117,msrc,uu____18119))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18128 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18128
                                      | uu____18129 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18130 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18131 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18131 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___201_18136 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___201_18136.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___201_18136.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___201_18136.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___201_18136.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___201_18136.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18137 = FStar_List.tl stack  in
                                    let uu____18138 =
                                      let uu____18139 =
                                        let uu____18146 =
                                          let uu____18147 =
                                            let uu____18160 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18160)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18147
                                           in
                                        FStar_Syntax_Syntax.mk uu____18146
                                         in
                                      uu____18139
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18137 uu____18138
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18176 =
                                      let uu____18177 = is_return body  in
                                      match uu____18177 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18181;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18182;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18185 -> false  in
                                    if uu____18176
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
                                         let uu____18206 =
                                           let uu____18213 =
                                             let uu____18214 =
                                               let uu____18231 =
                                                 let uu____18238 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18238]  in
                                               (uu____18231, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18214
                                              in
                                           FStar_Syntax_Syntax.mk uu____18213
                                            in
                                         uu____18206
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18272 =
                                           let uu____18273 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18273.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18272 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18279::uu____18280::[])
                                             ->
                                             let uu____18285 =
                                               let uu____18292 =
                                                 let uu____18293 =
                                                   let uu____18300 =
                                                     let uu____18301 =
                                                       let uu____18302 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18302
                                                        in
                                                     let uu____18303 =
                                                       let uu____18306 =
                                                         let uu____18307 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18307
                                                          in
                                                       [uu____18306]  in
                                                     uu____18301 ::
                                                       uu____18303
                                                      in
                                                   (bind1, uu____18300)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18293
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18292
                                                in
                                             uu____18285
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18313 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18325 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18325
                                         then
                                           let uu____18334 =
                                             let uu____18341 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18341
                                              in
                                           let uu____18342 =
                                             let uu____18351 =
                                               let uu____18358 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18358
                                                in
                                             [uu____18351]  in
                                           uu____18334 :: uu____18342
                                         else []  in
                                       let reified =
                                         let uu____18387 =
                                           let uu____18394 =
                                             let uu____18395 =
                                               let uu____18410 =
                                                 let uu____18419 =
                                                   let uu____18428 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18435 =
                                                     let uu____18444 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18444]  in
                                                   uu____18428 :: uu____18435
                                                    in
                                                 let uu____18469 =
                                                   let uu____18478 =
                                                     let uu____18487 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18494 =
                                                       let uu____18503 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18510 =
                                                         let uu____18519 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18526 =
                                                           let uu____18535 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18535]  in
                                                         uu____18519 ::
                                                           uu____18526
                                                          in
                                                       uu____18503 ::
                                                         uu____18510
                                                        in
                                                     uu____18487 ::
                                                       uu____18494
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18478
                                                    in
                                                 FStar_List.append
                                                   uu____18419 uu____18469
                                                  in
                                               (bind_inst, uu____18410)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18395
                                              in
                                           FStar_Syntax_Syntax.mk uu____18394
                                            in
                                         uu____18387
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18601  ->
                                            let uu____18602 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18603 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18602 uu____18603);
                                       (let uu____18604 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18604 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18628 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18628
                        in
                     let uu____18629 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18629 with
                      | (uu____18630,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18667 =
                                  let uu____18668 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18668.FStar_Syntax_Syntax.n  in
                                match uu____18667 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18672) -> t2
                                | uu____18677 -> head4  in
                              let uu____18678 =
                                let uu____18679 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18679.FStar_Syntax_Syntax.n  in
                              match uu____18678 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18685 -> FStar_Pervasives_Native.None
                               in
                            let uu____18686 = maybe_extract_fv head4  in
                            match uu____18686 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18696 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18696
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18701 = maybe_extract_fv head5
                                     in
                                  match uu____18701 with
                                  | FStar_Pervasives_Native.Some uu____18706
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18707 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18712 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18727 =
                              match uu____18727 with
                              | (e,q) ->
                                  let uu____18734 =
                                    let uu____18735 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18735.FStar_Syntax_Syntax.n  in
                                  (match uu____18734 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____18750 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____18750
                                   | uu____18751 -> false)
                               in
                            let uu____18752 =
                              let uu____18753 =
                                let uu____18762 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18762 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18753
                               in
                            if uu____18752
                            then
                              let uu____18781 =
                                let uu____18782 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18782
                                 in
                              failwith uu____18781
                            else ());
                           (let uu____18784 = maybe_unfold_action head_app
                               in
                            match uu____18784 with
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
                                   (fun uu____18827  ->
                                      let uu____18828 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18829 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18828 uu____18829);
                                 (let uu____18830 = FStar_List.tl stack  in
                                  norm cfg env uu____18830 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18832) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18856 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18856  in
                     (log cfg
                        (fun uu____18860  ->
                           let uu____18861 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18861);
                      (let uu____18862 = FStar_List.tl stack  in
                       norm cfg env uu____18862 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18983  ->
                               match uu____18983 with
                               | (pat,wopt,tm) ->
                                   let uu____19031 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19031)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19063 = FStar_List.tl stack  in
                     norm cfg env uu____19063 tm
                 | uu____19064 -> fallback ())

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
              (fun uu____19078  ->
                 let uu____19079 = FStar_Ident.string_of_lid msrc  in
                 let uu____19080 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19081 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19079
                   uu____19080 uu____19081);
            (let uu____19082 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19082
             then
               let ed =
                 let uu____19084 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19084  in
               let uu____19085 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19085 with
               | (uu____19086,return_repr) ->
                   let return_inst =
                     let uu____19099 =
                       let uu____19100 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19100.FStar_Syntax_Syntax.n  in
                     match uu____19099 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19106::[]) ->
                         let uu____19111 =
                           let uu____19118 =
                             let uu____19119 =
                               let uu____19126 =
                                 let uu____19127 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19127]  in
                               (return_tm, uu____19126)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19119  in
                           FStar_Syntax_Syntax.mk uu____19118  in
                         uu____19111 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19133 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19136 =
                     let uu____19143 =
                       let uu____19144 =
                         let uu____19159 =
                           let uu____19168 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19175 =
                             let uu____19184 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19184]  in
                           uu____19168 :: uu____19175  in
                         (return_inst, uu____19159)  in
                       FStar_Syntax_Syntax.Tm_app uu____19144  in
                     FStar_Syntax_Syntax.mk uu____19143  in
                   uu____19136 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19223 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19223 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19226 =
                      let uu____19227 = FStar_Ident.text_of_lid msrc  in
                      let uu____19228 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19227 uu____19228
                       in
                    failwith uu____19226
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19229;
                      FStar_TypeChecker_Env.mtarget = uu____19230;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19231;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19253 =
                      let uu____19254 = FStar_Ident.text_of_lid msrc  in
                      let uu____19255 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19254 uu____19255
                       in
                    failwith uu____19253
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19256;
                      FStar_TypeChecker_Env.mtarget = uu____19257;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19258;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____19293 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____19294 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____19293 t FStar_Syntax_Syntax.tun uu____19294))

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
                (fun uu____19350  ->
                   match uu____19350 with
                   | (a,imp) ->
                       let uu____19361 = norm cfg env [] a  in
                       (uu____19361, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____19369  ->
             let uu____19370 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____19371 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____19370 uu____19371);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19395 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____19395
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___202_19398 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___202_19398.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___202_19398.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19420 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____19420
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___203_19423 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___203_19423.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___203_19423.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____19460  ->
                      match uu____19460 with
                      | (a,i) ->
                          let uu____19471 = norm cfg env [] a  in
                          (uu____19471, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___116_19489  ->
                       match uu___116_19489 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____19493 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____19493
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___204_19501 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___205_19504 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___205_19504.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___204_19501.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___204_19501.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19507  ->
        match uu____19507 with
        | (x,imp) ->
            let uu____19510 =
              let uu___206_19511 = x  in
              let uu____19512 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___206_19511.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___206_19511.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19512
              }  in
            (uu____19510, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19518 =
          FStar_List.fold_left
            (fun uu____19552  ->
               fun b  ->
                 match uu____19552 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19518 with | (nbs,uu____19632) -> FStar_List.rev nbs

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
            let uu____19664 =
              let uu___207_19665 = rc  in
              let uu____19666 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___207_19665.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19666;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___207_19665.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19664
        | uu____19675 -> lopt

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
            (let uu____19696 = FStar_Syntax_Print.term_to_string tm  in
             let uu____19697 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____19696
               uu____19697)
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
          let uu____19719 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____19719
          then tm1
          else
            (let w t =
               let uu___208_19733 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___208_19733.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___208_19733.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____19744 =
                 let uu____19745 = FStar_Syntax_Util.unmeta t  in
                 uu____19745.FStar_Syntax_Syntax.n  in
               match uu____19744 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____19752 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____19801)::args1,(bv,uu____19804)::bs1) ->
                   let uu____19838 =
                     let uu____19839 = FStar_Syntax_Subst.compress t  in
                     uu____19839.FStar_Syntax_Syntax.n  in
                   (match uu____19838 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____19843 -> false)
               | ([],[]) -> true
               | (uu____19864,uu____19865) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19906 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19907 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____19906
                    uu____19907)
               else ();
               (let uu____19909 = FStar_Syntax_Util.head_and_args' t  in
                match uu____19909 with
                | (hd1,args) ->
                    let uu____19942 =
                      let uu____19943 = FStar_Syntax_Subst.compress hd1  in
                      uu____19943.FStar_Syntax_Syntax.n  in
                    (match uu____19942 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____19950 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____19951 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____19952 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____19950 uu____19951 uu____19952)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____19954 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19971 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19972 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____19971
                    uu____19972)
               else ();
               (let uu____19974 = FStar_Syntax_Util.is_squash t  in
                match uu____19974 with
                | FStar_Pervasives_Native.Some (uu____19985,t') ->
                    is_applied bs t'
                | uu____19997 ->
                    let uu____20006 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____20006 with
                     | FStar_Pervasives_Native.Some (uu____20017,t') ->
                         is_applied bs t'
                     | uu____20029 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20053 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20053 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20060)::(q,uu____20062)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20090 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20091 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20090 uu____20091)
                    else ();
                    (let uu____20093 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20093 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20098 =
                           let uu____20099 = FStar_Syntax_Subst.compress p
                              in
                           uu____20099.FStar_Syntax_Syntax.n  in
                         (match uu____20098 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20107 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20107))
                          | uu____20110 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20113)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20130 =
                           let uu____20131 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20131.FStar_Syntax_Syntax.n  in
                         (match uu____20130 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20139 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20139))
                          | uu____20142 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20146 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20146 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20151 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20151 with
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
                                     let uu____20162 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20162))
                               | uu____20165 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____20170)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____20187 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____20187 with
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
                                     let uu____20198 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20198))
                               | uu____20201 -> FStar_Pervasives_Native.None)
                          | uu____20204 -> FStar_Pervasives_Native.None)
                     | uu____20207 -> FStar_Pervasives_Native.None))
               | uu____20210 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____20223 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20223 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____20229)::[],uu____20230,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20241 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____20242 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____20241
                         uu____20242)
                    else ();
                    is_quantified_const bv phi')
               | uu____20244 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____20257 =
                 let uu____20258 = FStar_Syntax_Subst.compress phi  in
                 uu____20258.FStar_Syntax_Syntax.n  in
               match uu____20257 with
               | FStar_Syntax_Syntax.Tm_match (uu____20263,br::brs) ->
                   let uu____20330 = br  in
                   (match uu____20330 with
                    | (uu____20347,uu____20348,e) ->
                        let r =
                          let uu____20369 = simp_t e  in
                          match uu____20369 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____20375 =
                                FStar_List.for_all
                                  (fun uu____20393  ->
                                     match uu____20393 with
                                     | (uu____20406,uu____20407,e') ->
                                         let uu____20421 = simp_t e'  in
                                         uu____20421 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____20375
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____20429 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____20438 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____20438
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____20469 =
                 match uu____20469 with
                 | (t1,q) ->
                     let uu____20482 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____20482 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____20510 -> (t1, q))
                  in
               let uu____20521 = FStar_Syntax_Util.head_and_args t  in
               match uu____20521 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____20587 =
                 let uu____20588 = FStar_Syntax_Util.unmeta ty  in
                 uu____20588.FStar_Syntax_Syntax.n  in
               match uu____20587 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____20592) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____20597,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____20617 -> false  in
             let simplify1 arg =
               let uu____20642 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____20642, arg)  in
             let uu____20651 = is_forall_const tm1  in
             match uu____20651 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____20656 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____20657 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____20656
                       uu____20657)
                  else ();
                  (let uu____20659 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____20659))
             | FStar_Pervasives_Native.None  ->
                 let uu____20660 =
                   let uu____20661 = FStar_Syntax_Subst.compress tm1  in
                   uu____20661.FStar_Syntax_Syntax.n  in
                 (match uu____20660 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____20665;
                              FStar_Syntax_Syntax.vars = uu____20666;_},uu____20667);
                         FStar_Syntax_Syntax.pos = uu____20668;
                         FStar_Syntax_Syntax.vars = uu____20669;_},args)
                      ->
                      let uu____20695 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20695
                      then
                        let uu____20696 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20696 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20741)::
                             (uu____20742,(arg,uu____20744))::[] ->
                             maybe_auto_squash arg
                         | (uu____20793,(arg,uu____20795))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20796)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20845)::uu____20846::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20897::(FStar_Pervasives_Native.Some (false
                                         ),uu____20898)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20949 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20963 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20963
                         then
                           let uu____20964 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20964 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21009)::uu____21010::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21061::(FStar_Pervasives_Native.Some (true
                                           ),uu____21062)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21113)::(uu____21114,(arg,uu____21116))::[]
                               -> maybe_auto_squash arg
                           | (uu____21165,(arg,uu____21167))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21168)::[]
                               -> maybe_auto_squash arg
                           | uu____21217 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21231 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21231
                            then
                              let uu____21232 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21232 with
                              | uu____21277::(FStar_Pervasives_Native.Some
                                              (true ),uu____21278)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21329)::uu____21330::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21381)::(uu____21382,(arg,uu____21384))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21433,(p,uu____21435))::(uu____21436,
                                                                (q,uu____21438))::[]
                                  ->
                                  let uu____21485 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21485
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21487 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21501 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21501
                               then
                                 let uu____21502 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21502 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21547)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21548)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21599)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21600)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21651)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21652)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21703)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21704)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21755,(arg,uu____21757))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21758)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21807)::(uu____21808,(arg,uu____21810))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21859,(arg,uu____21861))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21862)::[]
                                     ->
                                     let uu____21911 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21911
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21912)::(uu____21913,(arg,uu____21915))::[]
                                     ->
                                     let uu____21964 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21964
                                 | (uu____21965,(p,uu____21967))::(uu____21968,
                                                                   (q,uu____21970))::[]
                                     ->
                                     let uu____22017 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22017
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22019 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22033 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22033
                                  then
                                    let uu____22034 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22034 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22079)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22110)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22141 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22155 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22155
                                     then
                                       match args with
                                       | (t,uu____22157)::[] ->
                                           let uu____22174 =
                                             let uu____22175 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22175.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22174 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22178::[],body,uu____22180)
                                                ->
                                                let uu____22207 = simp_t body
                                                   in
                                                (match uu____22207 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22210 -> tm1)
                                            | uu____22213 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22215))::(t,uu____22217)::[]
                                           ->
                                           let uu____22244 =
                                             let uu____22245 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22245.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22244 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22248::[],body,uu____22250)
                                                ->
                                                let uu____22277 = simp_t body
                                                   in
                                                (match uu____22277 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22280 -> tm1)
                                            | uu____22283 -> tm1)
                                       | uu____22284 -> tm1
                                     else
                                       (let uu____22294 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22294
                                        then
                                          match args with
                                          | (t,uu____22296)::[] ->
                                              let uu____22313 =
                                                let uu____22314 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22314.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22313 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22317::[],body,uu____22319)
                                                   ->
                                                   let uu____22346 =
                                                     simp_t body  in
                                                   (match uu____22346 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22349 -> tm1)
                                               | uu____22352 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22354))::(t,uu____22356)::[]
                                              ->
                                              let uu____22383 =
                                                let uu____22384 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22384.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22383 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22387::[],body,uu____22389)
                                                   ->
                                                   let uu____22416 =
                                                     simp_t body  in
                                                   (match uu____22416 with
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
                                                    | uu____22419 -> tm1)
                                               | uu____22422 -> tm1)
                                          | uu____22423 -> tm1
                                        else
                                          (let uu____22433 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22433
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22434;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22435;_},uu____22436)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22453;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22454;_},uu____22455)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22472 -> tm1
                                           else
                                             (let uu____22482 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22482 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22502 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22512;
                         FStar_Syntax_Syntax.vars = uu____22513;_},args)
                      ->
                      let uu____22535 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22535
                      then
                        let uu____22536 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22536 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22581)::
                             (uu____22582,(arg,uu____22584))::[] ->
                             maybe_auto_squash arg
                         | (uu____22633,(arg,uu____22635))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22636)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22685)::uu____22686::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22737::(FStar_Pervasives_Native.Some (false
                                         ),uu____22738)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22789 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22803 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22803
                         then
                           let uu____22804 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22804 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22849)::uu____22850::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22901::(FStar_Pervasives_Native.Some (true
                                           ),uu____22902)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22953)::(uu____22954,(arg,uu____22956))::[]
                               -> maybe_auto_squash arg
                           | (uu____23005,(arg,uu____23007))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____23008)::[]
                               -> maybe_auto_squash arg
                           | uu____23057 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23071 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23071
                            then
                              let uu____23072 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23072 with
                              | uu____23117::(FStar_Pervasives_Native.Some
                                              (true ),uu____23118)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23169)::uu____23170::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23221)::(uu____23222,(arg,uu____23224))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23273,(p,uu____23275))::(uu____23276,
                                                                (q,uu____23278))::[]
                                  ->
                                  let uu____23325 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23325
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23327 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23341 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23341
                               then
                                 let uu____23342 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23342 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23387)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23388)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23439)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23440)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23491)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23492)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23543)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23544)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23595,(arg,uu____23597))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23598)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23647)::(uu____23648,(arg,uu____23650))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23699,(arg,uu____23701))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23702)::[]
                                     ->
                                     let uu____23751 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23751
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23752)::(uu____23753,(arg,uu____23755))::[]
                                     ->
                                     let uu____23804 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23804
                                 | (uu____23805,(p,uu____23807))::(uu____23808,
                                                                   (q,uu____23810))::[]
                                     ->
                                     let uu____23857 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23857
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23859 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23873 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23873
                                  then
                                    let uu____23874 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23874 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23919)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23950)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23981 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23995 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23995
                                     then
                                       match args with
                                       | (t,uu____23997)::[] ->
                                           let uu____24014 =
                                             let uu____24015 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24015.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24014 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24018::[],body,uu____24020)
                                                ->
                                                let uu____24047 = simp_t body
                                                   in
                                                (match uu____24047 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24050 -> tm1)
                                            | uu____24053 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24055))::(t,uu____24057)::[]
                                           ->
                                           let uu____24084 =
                                             let uu____24085 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24085.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24084 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24088::[],body,uu____24090)
                                                ->
                                                let uu____24117 = simp_t body
                                                   in
                                                (match uu____24117 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24120 -> tm1)
                                            | uu____24123 -> tm1)
                                       | uu____24124 -> tm1
                                     else
                                       (let uu____24134 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24134
                                        then
                                          match args with
                                          | (t,uu____24136)::[] ->
                                              let uu____24153 =
                                                let uu____24154 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24154.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24153 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24157::[],body,uu____24159)
                                                   ->
                                                   let uu____24186 =
                                                     simp_t body  in
                                                   (match uu____24186 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24189 -> tm1)
                                               | uu____24192 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24194))::(t,uu____24196)::[]
                                              ->
                                              let uu____24223 =
                                                let uu____24224 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24224.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24223 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24227::[],body,uu____24229)
                                                   ->
                                                   let uu____24256 =
                                                     simp_t body  in
                                                   (match uu____24256 with
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
                                                    | uu____24259 -> tm1)
                                               | uu____24262 -> tm1)
                                          | uu____24263 -> tm1
                                        else
                                          (let uu____24273 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24273
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24274;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24275;_},uu____24276)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24293;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24294;_},uu____24295)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24312 -> tm1
                                           else
                                             (let uu____24322 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24322 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24342 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24357 = simp_t t  in
                      (match uu____24357 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24360 ->
                      let uu____24383 = is_const_match tm1  in
                      (match uu____24383 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24386 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____24396  ->
               (let uu____24398 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24399 = FStar_Syntax_Print.term_to_string t  in
                let uu____24400 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24407 =
                  let uu____24408 =
                    let uu____24411 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24411
                     in
                  stack_to_string uu____24408  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24398 uu____24399 uu____24400 uu____24407);
               (let uu____24434 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24434
                then
                  let uu____24435 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24435 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24442 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24443 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24444 =
                          let uu____24445 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24445
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24442
                          uu____24443 uu____24444);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____24463 =
                     let uu____24464 =
                       let uu____24465 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____24465  in
                     FStar_Util.string_of_int uu____24464  in
                   let uu____24470 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____24471 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____24463 uu____24470 uu____24471)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____24477,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____24528  ->
                     let uu____24529 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____24529);
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
               let uu____24567 =
                 let uu___209_24568 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___209_24568.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___209_24568.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____24567
           | (Arg (Univ uu____24571,uu____24572,uu____24573))::uu____24574 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____24577,uu____24578))::uu____24579 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____24594,uu____24595),aq,r))::stack1
               when
               let uu____24645 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24645 ->
               let t2 =
                 let uu____24649 =
                   let uu____24654 =
                     let uu____24655 = closure_as_term cfg env_arg tm  in
                     (uu____24655, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____24654  in
                 uu____24649 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____24665),aq,r))::stack1 ->
               (log cfg
                  (fun uu____24718  ->
                     let uu____24719 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____24719);
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
                  (let uu____24731 = FStar_ST.op_Bang m  in
                   match uu____24731 with
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
                   | FStar_Pervasives_Native.Some (uu____24874,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____24927 =
                 log cfg
                   (fun uu____24931  ->
                      let uu____24932 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____24932);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____24938 =
                 let uu____24939 = FStar_Syntax_Subst.compress t1  in
                 uu____24939.FStar_Syntax_Syntax.n  in
               (match uu____24938 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____24966 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____24966  in
                    (log cfg
                       (fun uu____24970  ->
                          let uu____24971 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____24971);
                     (let uu____24972 = FStar_List.tl stack  in
                      norm cfg env1 uu____24972 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____24973);
                       FStar_Syntax_Syntax.pos = uu____24974;
                       FStar_Syntax_Syntax.vars = uu____24975;_},(e,uu____24977)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____25006 when
                    (cfg.steps).primops ->
                    let uu____25021 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____25021 with
                     | (hd1,args) ->
                         let uu____25058 =
                           let uu____25059 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____25059.FStar_Syntax_Syntax.n  in
                         (match uu____25058 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____25063 = find_prim_step cfg fv  in
                              (match uu____25063 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____25066; arity = uu____25067;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____25069;
                                     requires_binder_substitution =
                                       uu____25070;
                                     interpretation = uu____25071;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____25086 -> fallback " (3)" ())
                          | uu____25089 -> fallback " (4)" ()))
                | uu____25090 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____25113  ->
                     let uu____25114 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____25114);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____25123 =
                   log cfg1
                     (fun uu____25128  ->
                        let uu____25129 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____25130 =
                          let uu____25131 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____25158  ->
                                    match uu____25158 with
                                    | (p,uu____25168,uu____25169) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____25131
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____25129 uu____25130);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___117_25186  ->
                                match uu___117_25186 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____25187 -> false))
                         in
                      let steps =
                        let uu___210_25189 = cfg1.steps  in
                        {
                          beta = (uu___210_25189.beta);
                          iota = (uu___210_25189.iota);
                          zeta = false;
                          weak = (uu___210_25189.weak);
                          hnf = (uu___210_25189.hnf);
                          primops = (uu___210_25189.primops);
                          do_not_unfold_pure_lets =
                            (uu___210_25189.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___210_25189.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___210_25189.pure_subterms_within_computations);
                          simplify = (uu___210_25189.simplify);
                          erase_universes = (uu___210_25189.erase_universes);
                          allow_unbound_universes =
                            (uu___210_25189.allow_unbound_universes);
                          reify_ = (uu___210_25189.reify_);
                          compress_uvars = (uu___210_25189.compress_uvars);
                          no_full_norm = (uu___210_25189.no_full_norm);
                          check_no_uvars = (uu___210_25189.check_no_uvars);
                          unmeta = (uu___210_25189.unmeta);
                          unascribe = (uu___210_25189.unascribe);
                          in_full_norm_request =
                            (uu___210_25189.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___210_25189.weakly_reduce_scrutinee)
                        }  in
                      let uu___211_25194 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___211_25194.tcenv);
                        debug = (uu___211_25194.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___211_25194.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___211_25194.memoize_lazy);
                        normalize_pure_lets =
                          (uu___211_25194.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____25266 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____25295 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____25379  ->
                                    fun uu____25380  ->
                                      match (uu____25379, uu____25380) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____25519 = norm_pat env3 p1
                                             in
                                          (match uu____25519 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____25295 with
                           | (pats1,env3) ->
                               ((let uu___212_25681 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___212_25681.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___213_25700 = x  in
                            let uu____25701 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___213_25700.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___213_25700.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25701
                            }  in
                          ((let uu___214_25715 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___214_25715.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___215_25726 = x  in
                            let uu____25727 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___215_25726.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___215_25726.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25727
                            }  in
                          ((let uu___216_25741 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___216_25741.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___217_25757 = x  in
                            let uu____25758 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___217_25757.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___217_25757.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25758
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___218_25773 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___218_25773.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____25817 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____25847 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____25847 with
                                  | (p,wopt,e) ->
                                      let uu____25867 = norm_pat env1 p  in
                                      (match uu____25867 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____25922 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____25922
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____25939 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____25939
                      then
                        norm
                          (let uu___219_25944 = cfg1  in
                           {
                             steps =
                               (let uu___220_25947 = cfg1.steps  in
                                {
                                  beta = (uu___220_25947.beta);
                                  iota = (uu___220_25947.iota);
                                  zeta = (uu___220_25947.zeta);
                                  weak = (uu___220_25947.weak);
                                  hnf = (uu___220_25947.hnf);
                                  primops = (uu___220_25947.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___220_25947.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___220_25947.unfold_until);
                                  unfold_only = (uu___220_25947.unfold_only);
                                  unfold_fully =
                                    (uu___220_25947.unfold_fully);
                                  unfold_attr = (uu___220_25947.unfold_attr);
                                  unfold_tac = (uu___220_25947.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___220_25947.pure_subterms_within_computations);
                                  simplify = (uu___220_25947.simplify);
                                  erase_universes =
                                    (uu___220_25947.erase_universes);
                                  allow_unbound_universes =
                                    (uu___220_25947.allow_unbound_universes);
                                  reify_ = (uu___220_25947.reify_);
                                  compress_uvars =
                                    (uu___220_25947.compress_uvars);
                                  no_full_norm =
                                    (uu___220_25947.no_full_norm);
                                  check_no_uvars =
                                    (uu___220_25947.check_no_uvars);
                                  unmeta = (uu___220_25947.unmeta);
                                  unascribe = (uu___220_25947.unascribe);
                                  in_full_norm_request =
                                    (uu___220_25947.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___219_25944.tcenv);
                             debug = (uu___219_25944.debug);
                             delta_level = (uu___219_25944.delta_level);
                             primitive_steps =
                               (uu___219_25944.primitive_steps);
                             strong = (uu___219_25944.strong);
                             memoize_lazy = (uu___219_25944.memoize_lazy);
                             normalize_pure_lets =
                               (uu___219_25944.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____25949 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____25949)
                    in
                 let rec is_cons head1 =
                   let uu____25974 =
                     let uu____25975 = FStar_Syntax_Subst.compress head1  in
                     uu____25975.FStar_Syntax_Syntax.n  in
                   match uu____25974 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____25979) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____25984 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25985;
                         FStar_Syntax_Syntax.fv_delta = uu____25986;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____25987;
                         FStar_Syntax_Syntax.fv_delta = uu____25988;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____25989);_}
                       -> true
                   | uu____25996 -> false  in
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
                   let uu____26159 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____26159 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____26246 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____26285 ->
                                 let uu____26286 =
                                   let uu____26287 = is_cons head1  in
                                   Prims.op_Negation uu____26287  in
                                 FStar_Util.Inr uu____26286)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____26312 =
                              let uu____26313 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____26313.FStar_Syntax_Syntax.n  in
                            (match uu____26312 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____26331 ->
                                 let uu____26332 =
                                   let uu____26333 = is_cons head1  in
                                   Prims.op_Negation uu____26333  in
                                 FStar_Util.Inr uu____26332))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____26410)::rest_a,(p1,uu____26413)::rest_p) ->
                       let uu____26457 = matches_pat t2 p1  in
                       (match uu____26457 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____26506 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____26624 = matches_pat scrutinee1 p1  in
                       (match uu____26624 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____26664  ->
                                  let uu____26665 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____26666 =
                                    let uu____26667 =
                                      FStar_List.map
                                        (fun uu____26677  ->
                                           match uu____26677 with
                                           | (uu____26682,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____26667
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____26665 uu____26666);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____26714  ->
                                       match uu____26714 with
                                       | (bv,t2) ->
                                           let uu____26737 =
                                             let uu____26744 =
                                               let uu____26747 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____26747
                                                in
                                             let uu____26748 =
                                               let uu____26749 =
                                                 let uu____26780 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____26780, false)
                                                  in
                                               Clos uu____26749  in
                                             (uu____26744, uu____26748)  in
                                           uu____26737 :: env2) env1 s
                                 in
                              let uu____26893 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____26893)))
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
    let uu____26920 =
      let uu____26923 = FStar_ST.op_Bang plugins  in p :: uu____26923  in
    FStar_ST.op_Colon_Equals plugins uu____26920  in
  let retrieve uu____27031 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____27108  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___118_27149  ->
                  match uu___118_27149 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____27153 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____27159 -> d  in
        let uu____27162 = to_fsteps s  in
        let uu____27163 =
          let uu____27164 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____27165 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____27166 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____27167 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____27168 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____27169 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____27170 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____27164;
            primop = uu____27165;
            unfolding = uu____27166;
            b380 = uu____27167;
            wpe = uu____27168;
            norm_delayed = uu____27169;
            print_normalized = uu____27170
          }  in
        let uu____27171 =
          let uu____27174 =
            let uu____27177 = retrieve_plugins ()  in
            FStar_List.append uu____27177 psteps  in
          add_steps built_in_primitive_steps uu____27174  in
        let uu____27180 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____27182 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____27182)
           in
        {
          steps = uu____27162;
          tcenv = e;
          debug = uu____27163;
          delta_level = d1;
          primitive_steps = uu____27171;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____27180
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
      fun t  -> let uu____27264 = config s e  in norm_comp uu____27264 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27281 = config [] env  in norm_universe uu____27281 [] u
  
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
        let uu____27305 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27305  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27312 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___221_27331 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___221_27331.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___221_27331.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27338 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27338
          then
            let ct1 =
              let uu____27340 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27340 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____27347 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27347
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___222_27351 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___222_27351.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___222_27351.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___222_27351.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___223_27353 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___223_27353.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___223_27353.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___223_27353.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___223_27353.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___224_27354 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___224_27354.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___224_27354.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27356 -> c
  
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
        let uu____27374 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27374  in
      let uu____27381 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____27381
      then
        let uu____27382 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____27382 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____27388  ->
                 let uu____27389 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____27389)
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
            ((let uu____27410 =
                let uu____27415 =
                  let uu____27416 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27416
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27415)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27410);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____27431 = config [AllowUnboundUniverses] env  in
          norm_comp uu____27431 [] c
        with
        | e ->
            ((let uu____27444 =
                let uu____27449 =
                  let uu____27450 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27450
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27449)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27444);
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
                   let uu____27495 =
                     let uu____27496 =
                       let uu____27503 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27503)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27496  in
                   mk uu____27495 t01.FStar_Syntax_Syntax.pos
               | uu____27508 -> t2)
          | uu____27509 -> t2  in
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
        let uu____27573 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27573 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27602 ->
                 let uu____27609 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27609 with
                  | (actuals,uu____27619,uu____27620) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27634 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27634 with
                         | (binders,args) ->
                             let uu____27645 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27645
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
      | uu____27659 ->
          let uu____27660 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27660 with
           | (head1,args) ->
               let uu____27697 =
                 let uu____27698 = FStar_Syntax_Subst.compress head1  in
                 uu____27698.FStar_Syntax_Syntax.n  in
               (match uu____27697 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27723 =
                      let uu____27736 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27736  in
                    (match uu____27723 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27766 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___229_27774 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___229_27774.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___229_27774.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___229_27774.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___229_27774.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___229_27774.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___229_27774.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___229_27774.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___229_27774.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___229_27774.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___229_27774.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___229_27774.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___229_27774.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___229_27774.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___229_27774.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___229_27774.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___229_27774.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___229_27774.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___229_27774.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___229_27774.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___229_27774.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___229_27774.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___229_27774.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___229_27774.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___229_27774.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___229_27774.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___229_27774.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___229_27774.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___229_27774.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___229_27774.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___229_27774.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___229_27774.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___229_27774.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___229_27774.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___229_27774.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___229_27774.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___229_27774.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____27766 with
                            | (uu____27775,ty,uu____27777) ->
                                eta_expand_with_type env t ty))
                | uu____27778 ->
                    let uu____27779 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___230_27787 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___230_27787.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___230_27787.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___230_27787.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___230_27787.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___230_27787.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___230_27787.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___230_27787.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___230_27787.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___230_27787.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___230_27787.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___230_27787.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___230_27787.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___230_27787.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___230_27787.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___230_27787.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___230_27787.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___230_27787.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___230_27787.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___230_27787.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___230_27787.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___230_27787.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___230_27787.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___230_27787.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___230_27787.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___230_27787.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___230_27787.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___230_27787.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___230_27787.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___230_27787.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___230_27787.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___230_27787.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___230_27787.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___230_27787.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___230_27787.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___230_27787.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___230_27787.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____27779 with
                     | (uu____27788,ty,uu____27790) ->
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
      let uu___231_27863 = x  in
      let uu____27864 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___231_27863.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___231_27863.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27864
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27867 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27892 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27893 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27894 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27895 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27902 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27903 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27904 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___232_27934 = rc  in
          let uu____27935 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27944 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___232_27934.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27935;
            FStar_Syntax_Syntax.residual_flags = uu____27944
          }  in
        let uu____27947 =
          let uu____27948 =
            let uu____27965 = elim_delayed_subst_binders bs  in
            let uu____27972 = elim_delayed_subst_term t2  in
            let uu____27975 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27965, uu____27972, uu____27975)  in
          FStar_Syntax_Syntax.Tm_abs uu____27948  in
        mk1 uu____27947
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28006 =
          let uu____28007 =
            let uu____28020 = elim_delayed_subst_binders bs  in
            let uu____28027 = elim_delayed_subst_comp c  in
            (uu____28020, uu____28027)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28007  in
        mk1 uu____28006
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28044 =
          let uu____28045 =
            let uu____28052 = elim_bv bv  in
            let uu____28053 = elim_delayed_subst_term phi  in
            (uu____28052, uu____28053)  in
          FStar_Syntax_Syntax.Tm_refine uu____28045  in
        mk1 uu____28044
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28080 =
          let uu____28081 =
            let uu____28096 = elim_delayed_subst_term t2  in
            let uu____28099 = elim_delayed_subst_args args  in
            (uu____28096, uu____28099)  in
          FStar_Syntax_Syntax.Tm_app uu____28081  in
        mk1 uu____28080
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___233_28167 = p  in
              let uu____28168 =
                let uu____28169 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28169  in
              {
                FStar_Syntax_Syntax.v = uu____28168;
                FStar_Syntax_Syntax.p =
                  (uu___233_28167.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___234_28171 = p  in
              let uu____28172 =
                let uu____28173 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28173  in
              {
                FStar_Syntax_Syntax.v = uu____28172;
                FStar_Syntax_Syntax.p =
                  (uu___234_28171.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___235_28180 = p  in
              let uu____28181 =
                let uu____28182 =
                  let uu____28189 = elim_bv x  in
                  let uu____28190 = elim_delayed_subst_term t0  in
                  (uu____28189, uu____28190)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28182  in
              {
                FStar_Syntax_Syntax.v = uu____28181;
                FStar_Syntax_Syntax.p =
                  (uu___235_28180.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___236_28213 = p  in
              let uu____28214 =
                let uu____28215 =
                  let uu____28228 =
                    FStar_List.map
                      (fun uu____28251  ->
                         match uu____28251 with
                         | (x,b) ->
                             let uu____28264 = elim_pat x  in
                             (uu____28264, b)) pats
                     in
                  (fv, uu____28228)  in
                FStar_Syntax_Syntax.Pat_cons uu____28215  in
              {
                FStar_Syntax_Syntax.v = uu____28214;
                FStar_Syntax_Syntax.p =
                  (uu___236_28213.FStar_Syntax_Syntax.p)
              }
          | uu____28277 -> p  in
        let elim_branch uu____28301 =
          match uu____28301 with
          | (pat,wopt,t3) ->
              let uu____28327 = elim_pat pat  in
              let uu____28330 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28333 = elim_delayed_subst_term t3  in
              (uu____28327, uu____28330, uu____28333)
           in
        let uu____28338 =
          let uu____28339 =
            let uu____28362 = elim_delayed_subst_term t2  in
            let uu____28365 = FStar_List.map elim_branch branches  in
            (uu____28362, uu____28365)  in
          FStar_Syntax_Syntax.Tm_match uu____28339  in
        mk1 uu____28338
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28496 =
          match uu____28496 with
          | (tc,topt) ->
              let uu____28531 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28541 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28541
                | FStar_Util.Inr c ->
                    let uu____28543 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28543
                 in
              let uu____28544 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28531, uu____28544)
           in
        let uu____28553 =
          let uu____28554 =
            let uu____28581 = elim_delayed_subst_term t2  in
            let uu____28584 = elim_ascription a  in
            (uu____28581, uu____28584, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28554  in
        mk1 uu____28553
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___237_28645 = lb  in
          let uu____28646 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28649 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___237_28645.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___237_28645.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28646;
            FStar_Syntax_Syntax.lbeff =
              (uu___237_28645.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28649;
            FStar_Syntax_Syntax.lbattrs =
              (uu___237_28645.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___237_28645.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28652 =
          let uu____28653 =
            let uu____28666 =
              let uu____28673 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28673)  in
            let uu____28682 = elim_delayed_subst_term t2  in
            (uu____28666, uu____28682)  in
          FStar_Syntax_Syntax.Tm_let uu____28653  in
        mk1 uu____28652
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28732 =
          let uu____28733 =
            let uu____28740 = elim_delayed_subst_term tm  in
            (uu____28740, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28733  in
        mk1 uu____28732
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28751 =
          let uu____28752 =
            let uu____28759 = elim_delayed_subst_term t2  in
            let uu____28762 = elim_delayed_subst_meta md  in
            (uu____28759, uu____28762)  in
          FStar_Syntax_Syntax.Tm_meta uu____28752  in
        mk1 uu____28751

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___119_28771  ->
         match uu___119_28771 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28775 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28775
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
        let uu____28798 =
          let uu____28799 =
            let uu____28808 = elim_delayed_subst_term t  in
            (uu____28808, uopt)  in
          FStar_Syntax_Syntax.Total uu____28799  in
        mk1 uu____28798
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28825 =
          let uu____28826 =
            let uu____28835 = elim_delayed_subst_term t  in
            (uu____28835, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28826  in
        mk1 uu____28825
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___238_28844 = ct  in
          let uu____28845 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28848 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28857 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___238_28844.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___238_28844.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28845;
            FStar_Syntax_Syntax.effect_args = uu____28848;
            FStar_Syntax_Syntax.flags = uu____28857
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___120_28860  ->
    match uu___120_28860 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____28872 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____28872
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28905 =
          let uu____28912 = elim_delayed_subst_term t  in (m, uu____28912)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28905
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28924 =
          let uu____28933 = elim_delayed_subst_term t  in
          (m1, m2, uu____28933)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28924
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____28960  ->
         match uu____28960 with
         | (t,q) ->
             let uu____28971 = elim_delayed_subst_term t  in (uu____28971, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28991  ->
         match uu____28991 with
         | (x,q) ->
             let uu____29002 =
               let uu___239_29003 = x  in
               let uu____29004 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___239_29003.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___239_29003.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29004
               }  in
             (uu____29002, q)) bs

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
            | (uu____29096,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29122,FStar_Util.Inl t) ->
                let uu____29140 =
                  let uu____29147 =
                    let uu____29148 =
                      let uu____29161 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29161)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29148  in
                  FStar_Syntax_Syntax.mk uu____29147  in
                uu____29140 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29175 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29175 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29205 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29268 ->
                    let uu____29269 =
                      let uu____29278 =
                        let uu____29279 = FStar_Syntax_Subst.compress t4  in
                        uu____29279.FStar_Syntax_Syntax.n  in
                      (uu____29278, tc)  in
                    (match uu____29269 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29306) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29347) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29386,FStar_Util.Inl uu____29387) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29414 -> failwith "Impossible")
                 in
              (match uu____29205 with
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
          let uu____29539 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29539 with
          | (univ_names1,binders1,tc) ->
              let uu____29605 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29605)
  
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
          let uu____29654 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29654 with
          | (univ_names1,binders1,tc) ->
              let uu____29720 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29720)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29759 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29759 with
           | (univ_names1,binders1,typ1) ->
               let uu___240_29793 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___240_29793.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___240_29793.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___240_29793.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___240_29793.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___241_29808 = s  in
          let uu____29809 =
            let uu____29810 =
              let uu____29819 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29819, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29810  in
          {
            FStar_Syntax_Syntax.sigel = uu____29809;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_29808.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_29808.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_29808.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_29808.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29836 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29836 with
           | (univ_names1,uu____29856,typ1) ->
               let uu___242_29874 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_29874.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_29874.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_29874.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_29874.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29880 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29880 with
           | (univ_names1,uu____29900,typ1) ->
               let uu___243_29918 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_29918.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_29918.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_29918.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_29918.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29946 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29946 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29971 =
                            let uu____29972 =
                              let uu____29973 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29973  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29972
                             in
                          elim_delayed_subst_term uu____29971  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___244_29976 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___244_29976.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___244_29976.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___244_29976.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___244_29976.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___245_29977 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___245_29977.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_29977.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_29977.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_29977.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___246_29983 = s  in
          let uu____29984 =
            let uu____29985 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29985  in
          {
            FStar_Syntax_Syntax.sigel = uu____29984;
            FStar_Syntax_Syntax.sigrng =
              (uu___246_29983.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_29983.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_29983.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_29983.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29989 = elim_uvars_aux_t env us [] t  in
          (match uu____29989 with
           | (us1,uu____30009,t1) ->
               let uu___247_30027 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___247_30027.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___247_30027.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___247_30027.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___247_30027.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____30028 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30030 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____30030 with
           | (univs1,binders,signature) ->
               let uu____30064 =
                 let uu____30069 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30069 with
                 | (univs_opening,univs2) ->
                     let uu____30092 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30092)
                  in
               (match uu____30064 with
                | (univs_opening,univs_closing) ->
                    let uu____30095 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30101 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30102 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30101, uu____30102)  in
                    (match uu____30095 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30126 =
                           match uu____30126 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30144 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30144 with
                                | (us1,t1) ->
                                    let uu____30155 =
                                      let uu____30164 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30175 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30164, uu____30175)  in
                                    (match uu____30155 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30204 =
                                           let uu____30213 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____30224 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____30213, uu____30224)  in
                                         (match uu____30204 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30254 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30254
                                                 in
                                              let uu____30255 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30255 with
                                               | (uu____30278,uu____30279,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30298 =
                                                       let uu____30299 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30299
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30298
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30308 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30308 with
                           | (uu____30325,uu____30326,t1) -> t1  in
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
                             | uu____30396 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30421 =
                               let uu____30422 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30422.FStar_Syntax_Syntax.n  in
                             match uu____30421 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30481 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30512 =
                               let uu____30513 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30513.FStar_Syntax_Syntax.n  in
                             match uu____30512 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30534) ->
                                 let uu____30555 = destruct_action_body body
                                    in
                                 (match uu____30555 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30600 ->
                                 let uu____30601 = destruct_action_body t  in
                                 (match uu____30601 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30650 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30650 with
                           | (action_univs,t) ->
                               let uu____30659 = destruct_action_typ_templ t
                                  in
                               (match uu____30659 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___248_30700 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___248_30700.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___248_30700.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___249_30702 = ed  in
                           let uu____30703 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30704 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30705 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30706 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30707 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30708 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30709 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____30710 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____30711 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____30712 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30713 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____30714 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30715 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30716 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___249_30702.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___249_30702.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____30703;
                             FStar_Syntax_Syntax.bind_wp = uu____30704;
                             FStar_Syntax_Syntax.if_then_else = uu____30705;
                             FStar_Syntax_Syntax.ite_wp = uu____30706;
                             FStar_Syntax_Syntax.stronger = uu____30707;
                             FStar_Syntax_Syntax.close_wp = uu____30708;
                             FStar_Syntax_Syntax.assert_p = uu____30709;
                             FStar_Syntax_Syntax.assume_p = uu____30710;
                             FStar_Syntax_Syntax.null_wp = uu____30711;
                             FStar_Syntax_Syntax.trivial = uu____30712;
                             FStar_Syntax_Syntax.repr = uu____30713;
                             FStar_Syntax_Syntax.return_repr = uu____30714;
                             FStar_Syntax_Syntax.bind_repr = uu____30715;
                             FStar_Syntax_Syntax.actions = uu____30716;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___249_30702.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___250_30719 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___250_30719.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___250_30719.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___250_30719.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___250_30719.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___121_30740 =
            match uu___121_30740 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30771 = elim_uvars_aux_t env us [] t  in
                (match uu____30771 with
                 | (us1,uu____30799,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___251_30826 = sub_eff  in
            let uu____30827 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30830 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___251_30826.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___251_30826.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30827;
              FStar_Syntax_Syntax.lift = uu____30830
            }  in
          let uu___252_30833 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___252_30833.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___252_30833.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___252_30833.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___252_30833.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____30843 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30843 with
           | (univ_names1,binders1,comp1) ->
               let uu___253_30877 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___253_30877.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___253_30877.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___253_30877.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___253_30877.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30880 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30881 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  