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
      fun uu___100_269  ->
        match uu___100_269 with
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
      let add_opt x uu___101_1503 =
        match uu___101_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___118_1523 = fs  in
          {
            beta = true;
            iota = (uu___118_1523.iota);
            zeta = (uu___118_1523.zeta);
            weak = (uu___118_1523.weak);
            hnf = (uu___118_1523.hnf);
            primops = (uu___118_1523.primops);
            do_not_unfold_pure_lets = (uu___118_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1523.unfold_until);
            unfold_only = (uu___118_1523.unfold_only);
            unfold_fully = (uu___118_1523.unfold_fully);
            unfold_attr = (uu___118_1523.unfold_attr);
            unfold_tac = (uu___118_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1523.pure_subterms_within_computations);
            simplify = (uu___118_1523.simplify);
            erase_universes = (uu___118_1523.erase_universes);
            allow_unbound_universes = (uu___118_1523.allow_unbound_universes);
            reify_ = (uu___118_1523.reify_);
            compress_uvars = (uu___118_1523.compress_uvars);
            no_full_norm = (uu___118_1523.no_full_norm);
            check_no_uvars = (uu___118_1523.check_no_uvars);
            unmeta = (uu___118_1523.unmeta);
            unascribe = (uu___118_1523.unascribe);
            in_full_norm_request = (uu___118_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___119_1524 = fs  in
          {
            beta = (uu___119_1524.beta);
            iota = true;
            zeta = (uu___119_1524.zeta);
            weak = (uu___119_1524.weak);
            hnf = (uu___119_1524.hnf);
            primops = (uu___119_1524.primops);
            do_not_unfold_pure_lets = (uu___119_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1524.unfold_until);
            unfold_only = (uu___119_1524.unfold_only);
            unfold_fully = (uu___119_1524.unfold_fully);
            unfold_attr = (uu___119_1524.unfold_attr);
            unfold_tac = (uu___119_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1524.pure_subterms_within_computations);
            simplify = (uu___119_1524.simplify);
            erase_universes = (uu___119_1524.erase_universes);
            allow_unbound_universes = (uu___119_1524.allow_unbound_universes);
            reify_ = (uu___119_1524.reify_);
            compress_uvars = (uu___119_1524.compress_uvars);
            no_full_norm = (uu___119_1524.no_full_norm);
            check_no_uvars = (uu___119_1524.check_no_uvars);
            unmeta = (uu___119_1524.unmeta);
            unascribe = (uu___119_1524.unascribe);
            in_full_norm_request = (uu___119_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___119_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___120_1525 = fs  in
          {
            beta = (uu___120_1525.beta);
            iota = (uu___120_1525.iota);
            zeta = true;
            weak = (uu___120_1525.weak);
            hnf = (uu___120_1525.hnf);
            primops = (uu___120_1525.primops);
            do_not_unfold_pure_lets = (uu___120_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1525.unfold_until);
            unfold_only = (uu___120_1525.unfold_only);
            unfold_fully = (uu___120_1525.unfold_fully);
            unfold_attr = (uu___120_1525.unfold_attr);
            unfold_tac = (uu___120_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1525.pure_subterms_within_computations);
            simplify = (uu___120_1525.simplify);
            erase_universes = (uu___120_1525.erase_universes);
            allow_unbound_universes = (uu___120_1525.allow_unbound_universes);
            reify_ = (uu___120_1525.reify_);
            compress_uvars = (uu___120_1525.compress_uvars);
            no_full_norm = (uu___120_1525.no_full_norm);
            check_no_uvars = (uu___120_1525.check_no_uvars);
            unmeta = (uu___120_1525.unmeta);
            unascribe = (uu___120_1525.unascribe);
            in_full_norm_request = (uu___120_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___121_1526 = fs  in
          {
            beta = false;
            iota = (uu___121_1526.iota);
            zeta = (uu___121_1526.zeta);
            weak = (uu___121_1526.weak);
            hnf = (uu___121_1526.hnf);
            primops = (uu___121_1526.primops);
            do_not_unfold_pure_lets = (uu___121_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___121_1526.unfold_until);
            unfold_only = (uu___121_1526.unfold_only);
            unfold_fully = (uu___121_1526.unfold_fully);
            unfold_attr = (uu___121_1526.unfold_attr);
            unfold_tac = (uu___121_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___121_1526.pure_subterms_within_computations);
            simplify = (uu___121_1526.simplify);
            erase_universes = (uu___121_1526.erase_universes);
            allow_unbound_universes = (uu___121_1526.allow_unbound_universes);
            reify_ = (uu___121_1526.reify_);
            compress_uvars = (uu___121_1526.compress_uvars);
            no_full_norm = (uu___121_1526.no_full_norm);
            check_no_uvars = (uu___121_1526.check_no_uvars);
            unmeta = (uu___121_1526.unmeta);
            unascribe = (uu___121_1526.unascribe);
            in_full_norm_request = (uu___121_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___121_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___122_1527 = fs  in
          {
            beta = (uu___122_1527.beta);
            iota = false;
            zeta = (uu___122_1527.zeta);
            weak = (uu___122_1527.weak);
            hnf = (uu___122_1527.hnf);
            primops = (uu___122_1527.primops);
            do_not_unfold_pure_lets = (uu___122_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___122_1527.unfold_until);
            unfold_only = (uu___122_1527.unfold_only);
            unfold_fully = (uu___122_1527.unfold_fully);
            unfold_attr = (uu___122_1527.unfold_attr);
            unfold_tac = (uu___122_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___122_1527.pure_subterms_within_computations);
            simplify = (uu___122_1527.simplify);
            erase_universes = (uu___122_1527.erase_universes);
            allow_unbound_universes = (uu___122_1527.allow_unbound_universes);
            reify_ = (uu___122_1527.reify_);
            compress_uvars = (uu___122_1527.compress_uvars);
            no_full_norm = (uu___122_1527.no_full_norm);
            check_no_uvars = (uu___122_1527.check_no_uvars);
            unmeta = (uu___122_1527.unmeta);
            unascribe = (uu___122_1527.unascribe);
            in_full_norm_request = (uu___122_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___122_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___123_1528 = fs  in
          {
            beta = (uu___123_1528.beta);
            iota = (uu___123_1528.iota);
            zeta = false;
            weak = (uu___123_1528.weak);
            hnf = (uu___123_1528.hnf);
            primops = (uu___123_1528.primops);
            do_not_unfold_pure_lets = (uu___123_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___123_1528.unfold_until);
            unfold_only = (uu___123_1528.unfold_only);
            unfold_fully = (uu___123_1528.unfold_fully);
            unfold_attr = (uu___123_1528.unfold_attr);
            unfold_tac = (uu___123_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___123_1528.pure_subterms_within_computations);
            simplify = (uu___123_1528.simplify);
            erase_universes = (uu___123_1528.erase_universes);
            allow_unbound_universes = (uu___123_1528.allow_unbound_universes);
            reify_ = (uu___123_1528.reify_);
            compress_uvars = (uu___123_1528.compress_uvars);
            no_full_norm = (uu___123_1528.no_full_norm);
            check_no_uvars = (uu___123_1528.check_no_uvars);
            unmeta = (uu___123_1528.unmeta);
            unascribe = (uu___123_1528.unascribe);
            in_full_norm_request = (uu___123_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___123_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___124_1530 = fs  in
          {
            beta = (uu___124_1530.beta);
            iota = (uu___124_1530.iota);
            zeta = (uu___124_1530.zeta);
            weak = true;
            hnf = (uu___124_1530.hnf);
            primops = (uu___124_1530.primops);
            do_not_unfold_pure_lets = (uu___124_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___124_1530.unfold_until);
            unfold_only = (uu___124_1530.unfold_only);
            unfold_fully = (uu___124_1530.unfold_fully);
            unfold_attr = (uu___124_1530.unfold_attr);
            unfold_tac = (uu___124_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___124_1530.pure_subterms_within_computations);
            simplify = (uu___124_1530.simplify);
            erase_universes = (uu___124_1530.erase_universes);
            allow_unbound_universes = (uu___124_1530.allow_unbound_universes);
            reify_ = (uu___124_1530.reify_);
            compress_uvars = (uu___124_1530.compress_uvars);
            no_full_norm = (uu___124_1530.no_full_norm);
            check_no_uvars = (uu___124_1530.check_no_uvars);
            unmeta = (uu___124_1530.unmeta);
            unascribe = (uu___124_1530.unascribe);
            in_full_norm_request = (uu___124_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___124_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___125_1531 = fs  in
          {
            beta = (uu___125_1531.beta);
            iota = (uu___125_1531.iota);
            zeta = (uu___125_1531.zeta);
            weak = (uu___125_1531.weak);
            hnf = true;
            primops = (uu___125_1531.primops);
            do_not_unfold_pure_lets = (uu___125_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___125_1531.unfold_until);
            unfold_only = (uu___125_1531.unfold_only);
            unfold_fully = (uu___125_1531.unfold_fully);
            unfold_attr = (uu___125_1531.unfold_attr);
            unfold_tac = (uu___125_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___125_1531.pure_subterms_within_computations);
            simplify = (uu___125_1531.simplify);
            erase_universes = (uu___125_1531.erase_universes);
            allow_unbound_universes = (uu___125_1531.allow_unbound_universes);
            reify_ = (uu___125_1531.reify_);
            compress_uvars = (uu___125_1531.compress_uvars);
            no_full_norm = (uu___125_1531.no_full_norm);
            check_no_uvars = (uu___125_1531.check_no_uvars);
            unmeta = (uu___125_1531.unmeta);
            unascribe = (uu___125_1531.unascribe);
            in_full_norm_request = (uu___125_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___125_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___126_1532 = fs  in
          {
            beta = (uu___126_1532.beta);
            iota = (uu___126_1532.iota);
            zeta = (uu___126_1532.zeta);
            weak = (uu___126_1532.weak);
            hnf = (uu___126_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___126_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1532.unfold_until);
            unfold_only = (uu___126_1532.unfold_only);
            unfold_fully = (uu___126_1532.unfold_fully);
            unfold_attr = (uu___126_1532.unfold_attr);
            unfold_tac = (uu___126_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1532.pure_subterms_within_computations);
            simplify = (uu___126_1532.simplify);
            erase_universes = (uu___126_1532.erase_universes);
            allow_unbound_universes = (uu___126_1532.allow_unbound_universes);
            reify_ = (uu___126_1532.reify_);
            compress_uvars = (uu___126_1532.compress_uvars);
            no_full_norm = (uu___126_1532.no_full_norm);
            check_no_uvars = (uu___126_1532.check_no_uvars);
            unmeta = (uu___126_1532.unmeta);
            unascribe = (uu___126_1532.unascribe);
            in_full_norm_request = (uu___126_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___127_1533 = fs  in
          {
            beta = (uu___127_1533.beta);
            iota = (uu___127_1533.iota);
            zeta = (uu___127_1533.zeta);
            weak = (uu___127_1533.weak);
            hnf = (uu___127_1533.hnf);
            primops = (uu___127_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___127_1533.unfold_until);
            unfold_only = (uu___127_1533.unfold_only);
            unfold_fully = (uu___127_1533.unfold_fully);
            unfold_attr = (uu___127_1533.unfold_attr);
            unfold_tac = (uu___127_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___127_1533.pure_subterms_within_computations);
            simplify = (uu___127_1533.simplify);
            erase_universes = (uu___127_1533.erase_universes);
            allow_unbound_universes = (uu___127_1533.allow_unbound_universes);
            reify_ = (uu___127_1533.reify_);
            compress_uvars = (uu___127_1533.compress_uvars);
            no_full_norm = (uu___127_1533.no_full_norm);
            check_no_uvars = (uu___127_1533.check_no_uvars);
            unmeta = (uu___127_1533.unmeta);
            unascribe = (uu___127_1533.unascribe);
            in_full_norm_request = (uu___127_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___127_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___128_1535 = fs  in
          {
            beta = (uu___128_1535.beta);
            iota = (uu___128_1535.iota);
            zeta = (uu___128_1535.zeta);
            weak = (uu___128_1535.weak);
            hnf = (uu___128_1535.hnf);
            primops = (uu___128_1535.primops);
            do_not_unfold_pure_lets = (uu___128_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___128_1535.unfold_only);
            unfold_fully = (uu___128_1535.unfold_fully);
            unfold_attr = (uu___128_1535.unfold_attr);
            unfold_tac = (uu___128_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_1535.pure_subterms_within_computations);
            simplify = (uu___128_1535.simplify);
            erase_universes = (uu___128_1535.erase_universes);
            allow_unbound_universes = (uu___128_1535.allow_unbound_universes);
            reify_ = (uu___128_1535.reify_);
            compress_uvars = (uu___128_1535.compress_uvars);
            no_full_norm = (uu___128_1535.no_full_norm);
            check_no_uvars = (uu___128_1535.check_no_uvars);
            unmeta = (uu___128_1535.unmeta);
            unascribe = (uu___128_1535.unascribe);
            in_full_norm_request = (uu___128_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___129_1539 = fs  in
          {
            beta = (uu___129_1539.beta);
            iota = (uu___129_1539.iota);
            zeta = (uu___129_1539.zeta);
            weak = (uu___129_1539.weak);
            hnf = (uu___129_1539.hnf);
            primops = (uu___129_1539.primops);
            do_not_unfold_pure_lets = (uu___129_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___129_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___129_1539.unfold_fully);
            unfold_attr = (uu___129_1539.unfold_attr);
            unfold_tac = (uu___129_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1539.pure_subterms_within_computations);
            simplify = (uu___129_1539.simplify);
            erase_universes = (uu___129_1539.erase_universes);
            allow_unbound_universes = (uu___129_1539.allow_unbound_universes);
            reify_ = (uu___129_1539.reify_);
            compress_uvars = (uu___129_1539.compress_uvars);
            no_full_norm = (uu___129_1539.no_full_norm);
            check_no_uvars = (uu___129_1539.check_no_uvars);
            unmeta = (uu___129_1539.unmeta);
            unascribe = (uu___129_1539.unascribe);
            in_full_norm_request = (uu___129_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___130_1545 = fs  in
          {
            beta = (uu___130_1545.beta);
            iota = (uu___130_1545.iota);
            zeta = (uu___130_1545.zeta);
            weak = (uu___130_1545.weak);
            hnf = (uu___130_1545.hnf);
            primops = (uu___130_1545.primops);
            do_not_unfold_pure_lets = (uu___130_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___130_1545.unfold_until);
            unfold_only = (uu___130_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___130_1545.unfold_attr);
            unfold_tac = (uu___130_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___130_1545.pure_subterms_within_computations);
            simplify = (uu___130_1545.simplify);
            erase_universes = (uu___130_1545.erase_universes);
            allow_unbound_universes = (uu___130_1545.allow_unbound_universes);
            reify_ = (uu___130_1545.reify_);
            compress_uvars = (uu___130_1545.compress_uvars);
            no_full_norm = (uu___130_1545.no_full_norm);
            check_no_uvars = (uu___130_1545.check_no_uvars);
            unmeta = (uu___130_1545.unmeta);
            unascribe = (uu___130_1545.unascribe);
            in_full_norm_request = (uu___130_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___130_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___131_1549 = fs  in
          {
            beta = (uu___131_1549.beta);
            iota = (uu___131_1549.iota);
            zeta = (uu___131_1549.zeta);
            weak = (uu___131_1549.weak);
            hnf = (uu___131_1549.hnf);
            primops = (uu___131_1549.primops);
            do_not_unfold_pure_lets = (uu___131_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___131_1549.unfold_until);
            unfold_only = (uu___131_1549.unfold_only);
            unfold_fully = (uu___131_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___131_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_1549.pure_subterms_within_computations);
            simplify = (uu___131_1549.simplify);
            erase_universes = (uu___131_1549.erase_universes);
            allow_unbound_universes = (uu___131_1549.allow_unbound_universes);
            reify_ = (uu___131_1549.reify_);
            compress_uvars = (uu___131_1549.compress_uvars);
            no_full_norm = (uu___131_1549.no_full_norm);
            check_no_uvars = (uu___131_1549.check_no_uvars);
            unmeta = (uu___131_1549.unmeta);
            unascribe = (uu___131_1549.unascribe);
            in_full_norm_request = (uu___131_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___132_1550 = fs  in
          {
            beta = (uu___132_1550.beta);
            iota = (uu___132_1550.iota);
            zeta = (uu___132_1550.zeta);
            weak = (uu___132_1550.weak);
            hnf = (uu___132_1550.hnf);
            primops = (uu___132_1550.primops);
            do_not_unfold_pure_lets = (uu___132_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___132_1550.unfold_until);
            unfold_only = (uu___132_1550.unfold_only);
            unfold_fully = (uu___132_1550.unfold_fully);
            unfold_attr = (uu___132_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___132_1550.pure_subterms_within_computations);
            simplify = (uu___132_1550.simplify);
            erase_universes = (uu___132_1550.erase_universes);
            allow_unbound_universes = (uu___132_1550.allow_unbound_universes);
            reify_ = (uu___132_1550.reify_);
            compress_uvars = (uu___132_1550.compress_uvars);
            no_full_norm = (uu___132_1550.no_full_norm);
            check_no_uvars = (uu___132_1550.check_no_uvars);
            unmeta = (uu___132_1550.unmeta);
            unascribe = (uu___132_1550.unascribe);
            in_full_norm_request = (uu___132_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___133_1551 = fs  in
          {
            beta = (uu___133_1551.beta);
            iota = (uu___133_1551.iota);
            zeta = (uu___133_1551.zeta);
            weak = (uu___133_1551.weak);
            hnf = (uu___133_1551.hnf);
            primops = (uu___133_1551.primops);
            do_not_unfold_pure_lets = (uu___133_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___133_1551.unfold_until);
            unfold_only = (uu___133_1551.unfold_only);
            unfold_fully = (uu___133_1551.unfold_fully);
            unfold_attr = (uu___133_1551.unfold_attr);
            unfold_tac = (uu___133_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___133_1551.simplify);
            erase_universes = (uu___133_1551.erase_universes);
            allow_unbound_universes = (uu___133_1551.allow_unbound_universes);
            reify_ = (uu___133_1551.reify_);
            compress_uvars = (uu___133_1551.compress_uvars);
            no_full_norm = (uu___133_1551.no_full_norm);
            check_no_uvars = (uu___133_1551.check_no_uvars);
            unmeta = (uu___133_1551.unmeta);
            unascribe = (uu___133_1551.unascribe);
            in_full_norm_request = (uu___133_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___134_1552 = fs  in
          {
            beta = (uu___134_1552.beta);
            iota = (uu___134_1552.iota);
            zeta = (uu___134_1552.zeta);
            weak = (uu___134_1552.weak);
            hnf = (uu___134_1552.hnf);
            primops = (uu___134_1552.primops);
            do_not_unfold_pure_lets = (uu___134_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___134_1552.unfold_until);
            unfold_only = (uu___134_1552.unfold_only);
            unfold_fully = (uu___134_1552.unfold_fully);
            unfold_attr = (uu___134_1552.unfold_attr);
            unfold_tac = (uu___134_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___134_1552.erase_universes);
            allow_unbound_universes = (uu___134_1552.allow_unbound_universes);
            reify_ = (uu___134_1552.reify_);
            compress_uvars = (uu___134_1552.compress_uvars);
            no_full_norm = (uu___134_1552.no_full_norm);
            check_no_uvars = (uu___134_1552.check_no_uvars);
            unmeta = (uu___134_1552.unmeta);
            unascribe = (uu___134_1552.unascribe);
            in_full_norm_request = (uu___134_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___135_1553 = fs  in
          {
            beta = (uu___135_1553.beta);
            iota = (uu___135_1553.iota);
            zeta = (uu___135_1553.zeta);
            weak = (uu___135_1553.weak);
            hnf = (uu___135_1553.hnf);
            primops = (uu___135_1553.primops);
            do_not_unfold_pure_lets = (uu___135_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___135_1553.unfold_until);
            unfold_only = (uu___135_1553.unfold_only);
            unfold_fully = (uu___135_1553.unfold_fully);
            unfold_attr = (uu___135_1553.unfold_attr);
            unfold_tac = (uu___135_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___135_1553.pure_subterms_within_computations);
            simplify = (uu___135_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___135_1553.allow_unbound_universes);
            reify_ = (uu___135_1553.reify_);
            compress_uvars = (uu___135_1553.compress_uvars);
            no_full_norm = (uu___135_1553.no_full_norm);
            check_no_uvars = (uu___135_1553.check_no_uvars);
            unmeta = (uu___135_1553.unmeta);
            unascribe = (uu___135_1553.unascribe);
            in_full_norm_request = (uu___135_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___135_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___136_1554 = fs  in
          {
            beta = (uu___136_1554.beta);
            iota = (uu___136_1554.iota);
            zeta = (uu___136_1554.zeta);
            weak = (uu___136_1554.weak);
            hnf = (uu___136_1554.hnf);
            primops = (uu___136_1554.primops);
            do_not_unfold_pure_lets = (uu___136_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___136_1554.unfold_until);
            unfold_only = (uu___136_1554.unfold_only);
            unfold_fully = (uu___136_1554.unfold_fully);
            unfold_attr = (uu___136_1554.unfold_attr);
            unfold_tac = (uu___136_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_1554.pure_subterms_within_computations);
            simplify = (uu___136_1554.simplify);
            erase_universes = (uu___136_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___136_1554.reify_);
            compress_uvars = (uu___136_1554.compress_uvars);
            no_full_norm = (uu___136_1554.no_full_norm);
            check_no_uvars = (uu___136_1554.check_no_uvars);
            unmeta = (uu___136_1554.unmeta);
            unascribe = (uu___136_1554.unascribe);
            in_full_norm_request = (uu___136_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___137_1555 = fs  in
          {
            beta = (uu___137_1555.beta);
            iota = (uu___137_1555.iota);
            zeta = (uu___137_1555.zeta);
            weak = (uu___137_1555.weak);
            hnf = (uu___137_1555.hnf);
            primops = (uu___137_1555.primops);
            do_not_unfold_pure_lets = (uu___137_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___137_1555.unfold_until);
            unfold_only = (uu___137_1555.unfold_only);
            unfold_fully = (uu___137_1555.unfold_fully);
            unfold_attr = (uu___137_1555.unfold_attr);
            unfold_tac = (uu___137_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_1555.pure_subterms_within_computations);
            simplify = (uu___137_1555.simplify);
            erase_universes = (uu___137_1555.erase_universes);
            allow_unbound_universes = (uu___137_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___137_1555.compress_uvars);
            no_full_norm = (uu___137_1555.no_full_norm);
            check_no_uvars = (uu___137_1555.check_no_uvars);
            unmeta = (uu___137_1555.unmeta);
            unascribe = (uu___137_1555.unascribe);
            in_full_norm_request = (uu___137_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___138_1556 = fs  in
          {
            beta = (uu___138_1556.beta);
            iota = (uu___138_1556.iota);
            zeta = (uu___138_1556.zeta);
            weak = (uu___138_1556.weak);
            hnf = (uu___138_1556.hnf);
            primops = (uu___138_1556.primops);
            do_not_unfold_pure_lets = (uu___138_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___138_1556.unfold_until);
            unfold_only = (uu___138_1556.unfold_only);
            unfold_fully = (uu___138_1556.unfold_fully);
            unfold_attr = (uu___138_1556.unfold_attr);
            unfold_tac = (uu___138_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_1556.pure_subterms_within_computations);
            simplify = (uu___138_1556.simplify);
            erase_universes = (uu___138_1556.erase_universes);
            allow_unbound_universes = (uu___138_1556.allow_unbound_universes);
            reify_ = (uu___138_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___138_1556.no_full_norm);
            check_no_uvars = (uu___138_1556.check_no_uvars);
            unmeta = (uu___138_1556.unmeta);
            unascribe = (uu___138_1556.unascribe);
            in_full_norm_request = (uu___138_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___139_1557 = fs  in
          {
            beta = (uu___139_1557.beta);
            iota = (uu___139_1557.iota);
            zeta = (uu___139_1557.zeta);
            weak = (uu___139_1557.weak);
            hnf = (uu___139_1557.hnf);
            primops = (uu___139_1557.primops);
            do_not_unfold_pure_lets = (uu___139_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___139_1557.unfold_until);
            unfold_only = (uu___139_1557.unfold_only);
            unfold_fully = (uu___139_1557.unfold_fully);
            unfold_attr = (uu___139_1557.unfold_attr);
            unfold_tac = (uu___139_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___139_1557.pure_subterms_within_computations);
            simplify = (uu___139_1557.simplify);
            erase_universes = (uu___139_1557.erase_universes);
            allow_unbound_universes = (uu___139_1557.allow_unbound_universes);
            reify_ = (uu___139_1557.reify_);
            compress_uvars = (uu___139_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___139_1557.check_no_uvars);
            unmeta = (uu___139_1557.unmeta);
            unascribe = (uu___139_1557.unascribe);
            in_full_norm_request = (uu___139_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___139_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___140_1558 = fs  in
          {
            beta = (uu___140_1558.beta);
            iota = (uu___140_1558.iota);
            zeta = (uu___140_1558.zeta);
            weak = (uu___140_1558.weak);
            hnf = (uu___140_1558.hnf);
            primops = (uu___140_1558.primops);
            do_not_unfold_pure_lets = (uu___140_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___140_1558.unfold_until);
            unfold_only = (uu___140_1558.unfold_only);
            unfold_fully = (uu___140_1558.unfold_fully);
            unfold_attr = (uu___140_1558.unfold_attr);
            unfold_tac = (uu___140_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___140_1558.pure_subterms_within_computations);
            simplify = (uu___140_1558.simplify);
            erase_universes = (uu___140_1558.erase_universes);
            allow_unbound_universes = (uu___140_1558.allow_unbound_universes);
            reify_ = (uu___140_1558.reify_);
            compress_uvars = (uu___140_1558.compress_uvars);
            no_full_norm = (uu___140_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___140_1558.unmeta);
            unascribe = (uu___140_1558.unascribe);
            in_full_norm_request = (uu___140_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___141_1559 = fs  in
          {
            beta = (uu___141_1559.beta);
            iota = (uu___141_1559.iota);
            zeta = (uu___141_1559.zeta);
            weak = (uu___141_1559.weak);
            hnf = (uu___141_1559.hnf);
            primops = (uu___141_1559.primops);
            do_not_unfold_pure_lets = (uu___141_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___141_1559.unfold_until);
            unfold_only = (uu___141_1559.unfold_only);
            unfold_fully = (uu___141_1559.unfold_fully);
            unfold_attr = (uu___141_1559.unfold_attr);
            unfold_tac = (uu___141_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___141_1559.pure_subterms_within_computations);
            simplify = (uu___141_1559.simplify);
            erase_universes = (uu___141_1559.erase_universes);
            allow_unbound_universes = (uu___141_1559.allow_unbound_universes);
            reify_ = (uu___141_1559.reify_);
            compress_uvars = (uu___141_1559.compress_uvars);
            no_full_norm = (uu___141_1559.no_full_norm);
            check_no_uvars = (uu___141_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___141_1559.unascribe);
            in_full_norm_request = (uu___141_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___142_1560 = fs  in
          {
            beta = (uu___142_1560.beta);
            iota = (uu___142_1560.iota);
            zeta = (uu___142_1560.zeta);
            weak = (uu___142_1560.weak);
            hnf = (uu___142_1560.hnf);
            primops = (uu___142_1560.primops);
            do_not_unfold_pure_lets = (uu___142_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1560.unfold_until);
            unfold_only = (uu___142_1560.unfold_only);
            unfold_fully = (uu___142_1560.unfold_fully);
            unfold_attr = (uu___142_1560.unfold_attr);
            unfold_tac = (uu___142_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1560.pure_subterms_within_computations);
            simplify = (uu___142_1560.simplify);
            erase_universes = (uu___142_1560.erase_universes);
            allow_unbound_universes = (uu___142_1560.allow_unbound_universes);
            reify_ = (uu___142_1560.reify_);
            compress_uvars = (uu___142_1560.compress_uvars);
            no_full_norm = (uu___142_1560.no_full_norm);
            check_no_uvars = (uu___142_1560.check_no_uvars);
            unmeta = (uu___142_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___142_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1560.weakly_reduce_scrutinee)
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
  
let (is_primop_app : cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg  ->
    fun tm  ->
      let uu____2391 = FStar_Syntax_Util.head_and_args tm  in
      match uu____2391 with
      | (head1,uu____2407) ->
          let uu____2428 =
            let uu____2429 = FStar_Syntax_Util.un_uinst head1  in
            uu____2429.FStar_Syntax_Syntax.n  in
          (match uu____2428 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____2433 = find_prim_step cfg fv  in
               (match uu____2433 with
                | FStar_Pervasives_Native.Some uu____2436 -> true
                | uu____2437 -> false)
           | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
               true
           | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
               uu____2440) -> true
           | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of ) ->
               true
           | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of
               ) -> true
           | uu____2441 -> false)
  
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
    match projectee with | Arg _0 -> true | uu____2599 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2637 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2675 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2748 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2798 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2856 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2900 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2940 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2978 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2996 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3023 = FStar_Syntax_Util.head_and_args' t  in
    match uu____3023 with | (hd1,uu____3037) -> hd1
  
let mk :
  'Auu____3060 .
    'Auu____3060 ->
      FStar_Range.range -> 'Auu____3060 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3123 = FStar_ST.op_Bang r  in
          match uu____3123 with
          | FStar_Pervasives_Native.Some uu____3175 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3251 =
      FStar_List.map
        (fun uu____3265  ->
           match uu____3265 with
           | (bopt,c) ->
               let uu____3278 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3280 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3278 uu____3280) env
       in
    FStar_All.pipe_right uu____3251 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___102_3283  ->
    match uu___102_3283 with
    | Clos (env,t,uu____3286,uu____3287) ->
        let uu____3332 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3339 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3332 uu____3339
    | Univ uu____3340 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___103_3345  ->
    match uu___103_3345 with
    | Arg (c,uu____3347,uu____3348) ->
        let uu____3349 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3349
    | MemoLazy uu____3350 -> "MemoLazy"
    | Abs (uu____3357,bs,uu____3359,uu____3360,uu____3361) ->
        let uu____3366 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3366
    | UnivArgs uu____3371 -> "UnivArgs"
    | Match uu____3378 -> "Match"
    | App (uu____3387,t,uu____3389,uu____3390) ->
        let uu____3391 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3391
    | Meta (uu____3392,m,uu____3394) -> "Meta"
    | Let uu____3395 -> "Let"
    | Cfg uu____3404 -> "Cfg"
    | Debug (t,uu____3406) ->
        let uu____3407 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3407
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3417 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3417 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3458 . 'Auu____3458 Prims.list -> Prims.bool =
  fun uu___104_3465  ->
    match uu___104_3465 with | [] -> true | uu____3468 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3500 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3500
      with
      | uu____3519 ->
          let uu____3520 =
            let uu____3521 = FStar_Syntax_Print.db_to_string x  in
            let uu____3522 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3521
              uu____3522
             in
          failwith uu____3520
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3530 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3530
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3534 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3534
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3538 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3538
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
          let uu____3572 =
            FStar_List.fold_left
              (fun uu____3598  ->
                 fun u1  ->
                   match uu____3598 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3623 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3623 with
                        | (k_u,n1) ->
                            let uu____3638 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3638
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3572 with
          | (uu____3656,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3683 =
                   let uu____3684 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3684  in
                 match uu____3683 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3702 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3710 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3716 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3725 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3734 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3741 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3741 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3758 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3758 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3766 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3774 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3774 with
                                  | (uu____3779,m) -> n1 <= m))
                           in
                        if uu____3766 then rest1 else us1
                    | uu____3784 -> us1)
               | uu____3789 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3793 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3793
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3797 = aux u  in
           match uu____3797 with
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
            (fun uu____3943  ->
               let uu____3944 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3945 = env_to_string env  in
               let uu____3946 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3944 uu____3945 uu____3946);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3955 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3958 ->
                    let uu____3983 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3983
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3984 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3985 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3986 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3987 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3988 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____4010 ->
                           let uu____4027 =
                             let uu____4028 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4029 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4028 uu____4029
                              in
                           failwith uu____4027
                       | uu____4032 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4038 =
                        let uu____4039 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4039  in
                      mk uu____4038 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4047 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4047  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4049 = lookup_bvar env x  in
                    (match uu____4049 with
                     | Univ uu____4052 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___147_4056 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___147_4056.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___147_4056.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4062,uu____4063) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4148  ->
                              fun stack1  ->
                                match uu____4148 with
                                | (a,aq) ->
                                    let uu____4160 =
                                      let uu____4161 =
                                        let uu____4168 =
                                          let uu____4169 =
                                            let uu____4200 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4200, false)  in
                                          Clos uu____4169  in
                                        (uu____4168, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4161  in
                                    uu____4160 :: stack1) args)
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
                    let uu____4394 = close_binders cfg env bs  in
                    (match uu____4394 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4441 =
                      let uu____4452 =
                        let uu____4459 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4459]  in
                      close_binders cfg env uu____4452  in
                    (match uu____4441 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4482 =
                             let uu____4483 =
                               let uu____4490 =
                                 let uu____4491 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4491
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4490, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4483  in
                           mk uu____4482 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4582 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4582
                      | FStar_Util.Inr c ->
                          let uu____4596 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4596
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4615 =
                        let uu____4616 =
                          let uu____4643 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4643, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4616  in
                      mk uu____4615 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4689 =
                            let uu____4690 =
                              let uu____4697 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4697, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4690  in
                          mk uu____4689 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4749  -> dummy :: env1) env
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
                    let uu____4770 =
                      let uu____4781 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4781
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4800 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___148_4816 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___148_4816.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___148_4816.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4800))
                       in
                    (match uu____4770 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___149_4834 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___149_4834.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___149_4834.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___149_4834.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___149_4834.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4848,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4911  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4936 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4936
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4956  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4980 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4980
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___150_4988 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___150_4988.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___150_4988.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___151_4989 = lb  in
                      let uu____4990 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___151_4989.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___151_4989.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4990;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___151_4989.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___151_4989.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5022  -> fun env1  -> dummy :: env1)
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
            (fun uu____5125  ->
               let uu____5126 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5127 = env_to_string env  in
               let uu____5128 = stack_to_string stack  in
               let uu____5129 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5126 uu____5127 uu____5128 uu____5129);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5134,uu____5135),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5210 = close_binders cfg env' bs  in
               (match uu____5210 with
                | (bs1,uu____5224) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5240 =
                      let uu___152_5241 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___152_5241.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___152_5241.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5240)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5287 =
                 match uu____5287 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5362 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5383 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5443  ->
                                     fun uu____5444  ->
                                       match (uu____5443, uu____5444) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5535 = norm_pat env4 p1
                                              in
                                           (match uu____5535 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5383 with
                            | (pats1,env4) ->
                                ((let uu___153_5617 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___153_5617.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___154_5636 = x  in
                             let uu____5637 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___154_5636.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___154_5636.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5637
                             }  in
                           ((let uu___155_5651 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___155_5651.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___156_5662 = x  in
                             let uu____5663 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___156_5662.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___156_5662.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5663
                             }  in
                           ((let uu___157_5677 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___157_5677.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___158_5693 = x  in
                             let uu____5694 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_5693.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_5693.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5694
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___159_5703 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___159_5703.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5708 = norm_pat env2 pat  in
                     (match uu____5708 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5753 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5753
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5772 =
                   let uu____5773 =
                     let uu____5796 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5796)  in
                   FStar_Syntax_Syntax.Tm_match uu____5773  in
                 mk uu____5772 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5891 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5980  ->
                                       match uu____5980 with
                                       | (a,q) ->
                                           let uu____5999 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5999, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5891
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6010 =
                       let uu____6017 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6017)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6010
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6029 =
                       let uu____6038 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6038)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6029
                 | uu____6043 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6047 -> failwith "Impossible: unexpected stack element")

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
        let uu____6061 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6110  ->
                  fun uu____6111  ->
                    match (uu____6110, uu____6111) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___160_6181 = b  in
                          let uu____6182 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___160_6181.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___160_6181.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6182
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6061 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6275 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6288 = inline_closure_env cfg env [] t  in
                 let uu____6289 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6288 uu____6289
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6302 = inline_closure_env cfg env [] t  in
                 let uu____6303 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6302 uu____6303
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6349  ->
                           match uu____6349 with
                           | (a,q) ->
                               let uu____6362 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6362, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___105_6377  ->
                           match uu___105_6377 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6381 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6381
                           | f -> f))
                    in
                 let uu____6385 =
                   let uu___161_6386 = c1  in
                   let uu____6387 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6387;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___161_6386.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6385)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___106_6397  ->
            match uu___106_6397 with
            | FStar_Syntax_Syntax.DECREASES uu____6398 -> false
            | uu____6401 -> true))

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
                   (fun uu___107_6419  ->
                      match uu___107_6419 with
                      | FStar_Syntax_Syntax.DECREASES uu____6420 -> false
                      | uu____6423 -> true))
               in
            let rc1 =
              let uu___162_6425 = rc  in
              let uu____6426 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___162_6425.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6426;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6435 -> lopt

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
    let uu____6548 =
      let uu____6557 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6557  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6548  in
  let arg_as_bounded_int uu____6583 =
    match uu____6583 with
    | (a,uu____6595) ->
        let uu____6602 =
          let uu____6603 = FStar_Syntax_Subst.compress a  in
          uu____6603.FStar_Syntax_Syntax.n  in
        (match uu____6602 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6613;
                FStar_Syntax_Syntax.vars = uu____6614;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6616;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6617;_},uu____6618)::[])
             when
             let uu____6657 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6657 "int_to_t" ->
             let uu____6658 =
               let uu____6663 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6663)  in
             FStar_Pervasives_Native.Some uu____6658
         | uu____6668 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6716 = f a  in FStar_Pervasives_Native.Some uu____6716
    | uu____6717 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6773 = f a0 a1  in FStar_Pervasives_Native.Some uu____6773
    | uu____6774 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6832 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6832  in
  let binary_op as_a f res args =
    let uu____6897 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6897  in
  let as_primitive_step is_strong uu____6928 =
    match uu____6928 with
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
           let uu____6988 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6988)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7024 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7024)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7053 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7053)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7089 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7089)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7125 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7125)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7257 =
          let uu____7266 = as_a a  in
          let uu____7269 = as_b b  in (uu____7266, uu____7269)  in
        (match uu____7257 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7284 =
               let uu____7285 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7285  in
             FStar_Pervasives_Native.Some uu____7284
         | uu____7286 -> FStar_Pervasives_Native.None)
    | uu____7295 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7315 =
        let uu____7316 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7316  in
      mk uu____7315 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7328 =
      let uu____7331 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7331  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7328  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7373 =
      let uu____7374 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7374  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7373
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7396 = arg_as_string a1  in
        (match uu____7396 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7402 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7402 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7415 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7415
              | uu____7416 -> FStar_Pervasives_Native.None)
         | uu____7421 -> FStar_Pervasives_Native.None)
    | uu____7424 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7438 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7438
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7475 =
          let uu____7496 = arg_as_string fn  in
          let uu____7499 = arg_as_int from_line  in
          let uu____7502 = arg_as_int from_col  in
          let uu____7505 = arg_as_int to_line  in
          let uu____7508 = arg_as_int to_col  in
          (uu____7496, uu____7499, uu____7502, uu____7505, uu____7508)  in
        (match uu____7475 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7539 =
                 let uu____7540 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7541 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7540 uu____7541  in
               let uu____7542 =
                 let uu____7543 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7544 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7543 uu____7544  in
               FStar_Range.mk_range fn1 uu____7539 uu____7542  in
             let uu____7545 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7545
         | uu____7546 -> FStar_Pervasives_Native.None)
    | uu____7567 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7600)::(a1,uu____7602)::(a2,uu____7604)::[] ->
        let uu____7641 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7641 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7654 -> FStar_Pervasives_Native.None)
    | uu____7655 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7686)::[] ->
        let uu____7695 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7695 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7701 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7701
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7702 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7728 =
      let uu____7745 =
        let uu____7762 =
          let uu____7779 =
            let uu____7796 =
              let uu____7813 =
                let uu____7830 =
                  let uu____7847 =
                    let uu____7864 =
                      let uu____7881 =
                        let uu____7898 =
                          let uu____7915 =
                            let uu____7932 =
                              let uu____7949 =
                                let uu____7966 =
                                  let uu____7983 =
                                    let uu____8000 =
                                      let uu____8017 =
                                        let uu____8034 =
                                          let uu____8051 =
                                            let uu____8068 =
                                              let uu____8085 =
                                                let uu____8100 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8100,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8109 =
                                                let uu____8126 =
                                                  let uu____8141 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8141,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8154 =
                                                  let uu____8171 =
                                                    let uu____8188 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8188,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8199 =
                                                    let uu____8218 =
                                                      let uu____8235 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8235,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8218]  in
                                                  uu____8171 :: uu____8199
                                                   in
                                                uu____8126 :: uu____8154  in
                                              uu____8085 :: uu____8109  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8068
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8051
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8034
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8017
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8000
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8463 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8463 y)))
                                    :: uu____7983
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7966
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7949
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7932
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7915
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7898
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7881
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8658 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8658)))
                      :: uu____7864
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8688 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8688)))
                    :: uu____7847
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8718 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8718)))
                  :: uu____7830
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8748 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8748)))
                :: uu____7813
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7796
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7779
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7762
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7745
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7728
     in
  let weak_ops =
    let uu____8909 =
      let uu____8930 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8930, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8909]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9028 =
        let uu____9033 =
          let uu____9034 = FStar_Syntax_Syntax.as_arg c  in [uu____9034]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9033  in
      uu____9028 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9090 =
                let uu____9105 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9105, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9127  ->
                          fun uu____9128  ->
                            match (uu____9127, uu____9128) with
                            | ((int_to_t1,x),(uu____9147,y)) ->
                                let uu____9157 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9157)))
                 in
              let uu____9158 =
                let uu____9175 =
                  let uu____9190 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9190, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9212  ->
                            fun uu____9213  ->
                              match (uu____9212, uu____9213) with
                              | ((int_to_t1,x),(uu____9232,y)) ->
                                  let uu____9242 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9242)))
                   in
                let uu____9243 =
                  let uu____9260 =
                    let uu____9275 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9275, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9297  ->
                              fun uu____9298  ->
                                match (uu____9297, uu____9298) with
                                | ((int_to_t1,x),(uu____9317,y)) ->
                                    let uu____9327 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9327)))
                     in
                  let uu____9328 =
                    let uu____9345 =
                      let uu____9360 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9360, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9378  ->
                                match uu____9378 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9345]  in
                  uu____9260 :: uu____9328  in
                uu____9175 :: uu____9243  in
              uu____9090 :: uu____9158))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9508 =
                let uu____9523 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9523, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9545  ->
                          fun uu____9546  ->
                            match (uu____9545, uu____9546) with
                            | ((int_to_t1,x),(uu____9565,y)) ->
                                let uu____9575 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9575)))
                 in
              let uu____9576 =
                let uu____9593 =
                  let uu____9608 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9608, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9630  ->
                            fun uu____9631  ->
                              match (uu____9630, uu____9631) with
                              | ((int_to_t1,x),(uu____9650,y)) ->
                                  let uu____9660 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9660)))
                   in
                [uu____9593]  in
              uu____9508 :: uu____9576))
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
    | (_typ,uu____9790)::(a1,uu____9792)::(a2,uu____9794)::[] ->
        let uu____9831 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9831 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___163_9837 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___163_9837.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___163_9837.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___164_9841 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___164_9841.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___164_9841.FStar_Syntax_Syntax.vars)
                })
         | uu____9842 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9844)::uu____9845::(a1,uu____9847)::(a2,uu____9849)::[] ->
        let uu____9898 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9898 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___163_9904 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___163_9904.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___163_9904.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___164_9908 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___164_9908.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___164_9908.FStar_Syntax_Syntax.vars)
                })
         | uu____9909 -> FStar_Pervasives_Native.None)
    | uu____9910 -> failwith "Unexpected number of arguments"  in
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
    let uu____9964 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9964 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10016 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10016) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10078  ->
           fun subst1  ->
             match uu____10078 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10119,uu____10120)) ->
                      let uu____10179 = b  in
                      (match uu____10179 with
                       | (bv,uu____10187) ->
                           let uu____10188 =
                             let uu____10189 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10189  in
                           if uu____10188
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10194 = unembed_binder term1  in
                              match uu____10194 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10201 =
                                      let uu___165_10202 = bv  in
                                      let uu____10203 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___165_10202.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___165_10202.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10203
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10201
                                     in
                                  let b_for_x =
                                    let uu____10207 =
                                      let uu____10214 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10214)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10207  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___108_10224  ->
                                         match uu___108_10224 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10225,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10227;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10228;_})
                                             ->
                                             let uu____10233 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10233
                                         | uu____10234 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10235 -> subst1)) env []
  
let reduce_primops :
  'Auu____10258 'Auu____10259 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10258) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10259 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then
            (log_primops cfg
               (fun uu____10307  ->
                  let uu____10308 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "primop: skipping for %s\n" uu____10308);
             tm)
          else
            (let uu____10310 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10310 with
             | (head1,args) ->
                 let uu____10347 =
                   let uu____10348 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10348.FStar_Syntax_Syntax.n  in
                 (match uu____10347 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10352 = find_prim_step cfg fv  in
                      (match uu____10352 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10374  ->
                                   let uu____10375 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10376 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10383 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10375 uu____10376 uu____10383);
                              tm)
                           else
                             (let uu____10385 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10385 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10496  ->
                                        let uu____10497 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10497);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10500  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10502 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10502 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10508  ->
                                              let uu____10509 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10509);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10515  ->
                                              let uu____10516 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10517 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10516 uu____10517);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10518 ->
                           (log_primops cfg
                              (fun uu____10522  ->
                                 let uu____10523 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10523);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10527  ->
                            let uu____10528 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10528);
                       (match args with
                        | (a1,uu____10530)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10547 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10559  ->
                            let uu____10560 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10560);
                       (match args with
                        | (t,uu____10562)::(r,uu____10564)::[] ->
                            let uu____10591 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10591 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___166_10595 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___166_10595.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___166_10595.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10598 -> tm))
                  | uu____10607 -> tm))
  
let reduce_equality :
  'Auu____10618 'Auu____10619 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10618) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10619 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___167_10663 = cfg  in
         {
           steps =
             (let uu___168_10666 = default_steps  in
              {
                beta = (uu___168_10666.beta);
                iota = (uu___168_10666.iota);
                zeta = (uu___168_10666.zeta);
                weak = (uu___168_10666.weak);
                hnf = (uu___168_10666.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___168_10666.do_not_unfold_pure_lets);
                unfold_until = (uu___168_10666.unfold_until);
                unfold_only = (uu___168_10666.unfold_only);
                unfold_fully = (uu___168_10666.unfold_fully);
                unfold_attr = (uu___168_10666.unfold_attr);
                unfold_tac = (uu___168_10666.unfold_tac);
                pure_subterms_within_computations =
                  (uu___168_10666.pure_subterms_within_computations);
                simplify = (uu___168_10666.simplify);
                erase_universes = (uu___168_10666.erase_universes);
                allow_unbound_universes =
                  (uu___168_10666.allow_unbound_universes);
                reify_ = (uu___168_10666.reify_);
                compress_uvars = (uu___168_10666.compress_uvars);
                no_full_norm = (uu___168_10666.no_full_norm);
                check_no_uvars = (uu___168_10666.check_no_uvars);
                unmeta = (uu___168_10666.unmeta);
                unascribe = (uu___168_10666.unascribe);
                in_full_norm_request = (uu___168_10666.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___168_10666.weakly_reduce_scrutinee)
              });
           tcenv = (uu___167_10663.tcenv);
           debug = (uu___167_10663.debug);
           delta_level = (uu___167_10663.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___167_10663.strong);
           memoize_lazy = (uu___167_10663.memoize_lazy);
           normalize_pure_lets = (uu___167_10663.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10673 .
    FStar_Syntax_Syntax.term -> 'Auu____10673 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10688 =
        let uu____10695 =
          let uu____10696 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10696.FStar_Syntax_Syntax.n  in
        (uu____10695, args)  in
      match uu____10688 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10702::uu____10703::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10707::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10712::uu____10713::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10716 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___109_10729  ->
    match uu___109_10729 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10735 =
          let uu____10738 =
            let uu____10739 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10739  in
          [uu____10738]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10735
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10745 =
          let uu____10748 =
            let uu____10749 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10749  in
          [uu____10748]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10745
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10770 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10770) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10816 =
          let uu____10821 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10821 s  in
        match uu____10816 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10837 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10837
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10854::(tm,uu____10856)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10885)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10906)::uu____10907::(tm,uu____10909)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10950 =
            let uu____10955 = full_norm steps  in parse_steps uu____10955  in
          (match uu____10950 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10994 -> FStar_Pervasives_Native.None
  
let firstn :
  'Auu____11013 .
    Prims.int ->
      'Auu____11013 Prims.list ->
        ('Auu____11013 Prims.list,'Auu____11013 Prims.list)
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
          (uu____11055,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11056;
                         FStar_Syntax_Syntax.vars = uu____11057;_},uu____11058,uu____11059))::uu____11060
          -> (cfg.steps).reify_
      | uu____11067 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11090) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11100) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11119  ->
                  match uu____11119 with
                  | (a,uu____11127) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11133 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11158 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11159 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11176 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11177 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11178 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11179 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11180 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11181 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11188 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11195 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11208 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11225 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11238 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11245 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11307  ->
                   match uu____11307 with
                   | (a,uu____11315) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11322) ->
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
                     (fun uu____11444  ->
                        match uu____11444 with
                        | (a,uu____11452) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11457,uu____11458,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11464,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11470 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11477 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11478 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11770 ->
                   let uu____11795 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11795
               | uu____11796 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11804  ->
               let uu____11805 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11806 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11807 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11814 =
                 let uu____11815 =
                   let uu____11818 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11818
                    in
                 stack_to_string uu____11815  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11805 uu____11806 uu____11807 uu____11814);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11841 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11842 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11843 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11844;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____11845;_}
               when _0_17 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11848;
                 FStar_Syntax_Syntax.fv_delta = uu____11849;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11850;
                 FStar_Syntax_Syntax.fv_delta = uu____11851;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11852);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11859 ->
               let uu____11866 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11866
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11896 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11896)
               ->
               let cfg' =
                 let uu___169_11898 = cfg  in
                 {
                   steps =
                     (let uu___170_11901 = cfg.steps  in
                      {
                        beta = (uu___170_11901.beta);
                        iota = (uu___170_11901.iota);
                        zeta = (uu___170_11901.zeta);
                        weak = (uu___170_11901.weak);
                        hnf = (uu___170_11901.hnf);
                        primops = (uu___170_11901.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___170_11901.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___170_11901.unfold_attr);
                        unfold_tac = (uu___170_11901.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___170_11901.pure_subterms_within_computations);
                        simplify = (uu___170_11901.simplify);
                        erase_universes = (uu___170_11901.erase_universes);
                        allow_unbound_universes =
                          (uu___170_11901.allow_unbound_universes);
                        reify_ = (uu___170_11901.reify_);
                        compress_uvars = (uu___170_11901.compress_uvars);
                        no_full_norm = (uu___170_11901.no_full_norm);
                        check_no_uvars = (uu___170_11901.check_no_uvars);
                        unmeta = (uu___170_11901.unmeta);
                        unascribe = (uu___170_11901.unascribe);
                        in_full_norm_request =
                          (uu___170_11901.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___170_11901.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___169_11898.tcenv);
                   debug = (uu___169_11898.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___169_11898.primitive_steps);
                   strong = (uu___169_11898.strong);
                   memoize_lazy = (uu___169_11898.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11906 = get_norm_request (norm cfg' env []) args  in
               (match uu____11906 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11937  ->
                              fun stack1  ->
                                match uu____11937 with
                                | (a,aq) ->
                                    let uu____11949 =
                                      let uu____11950 =
                                        let uu____11957 =
                                          let uu____11958 =
                                            let uu____11989 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11989, false)  in
                                          Clos uu____11958  in
                                        (uu____11957, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11950  in
                                    uu____11949 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12073  ->
                          let uu____12074 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12074);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12096 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___110_12101  ->
                                match uu___110_12101 with
                                | UnfoldUntil uu____12102 -> true
                                | UnfoldOnly uu____12103 -> true
                                | UnfoldFully uu____12106 -> true
                                | uu____12109 -> false))
                         in
                      if uu____12096
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___171_12114 = cfg  in
                      let uu____12115 =
                        let uu___172_12116 = to_fsteps s  in
                        {
                          beta = (uu___172_12116.beta);
                          iota = (uu___172_12116.iota);
                          zeta = (uu___172_12116.zeta);
                          weak = (uu___172_12116.weak);
                          hnf = (uu___172_12116.hnf);
                          primops = (uu___172_12116.primops);
                          do_not_unfold_pure_lets =
                            (uu___172_12116.do_not_unfold_pure_lets);
                          unfold_until = (uu___172_12116.unfold_until);
                          unfold_only = (uu___172_12116.unfold_only);
                          unfold_fully = (uu___172_12116.unfold_fully);
                          unfold_attr = (uu___172_12116.unfold_attr);
                          unfold_tac = (uu___172_12116.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___172_12116.pure_subterms_within_computations);
                          simplify = (uu___172_12116.simplify);
                          erase_universes = (uu___172_12116.erase_universes);
                          allow_unbound_universes =
                            (uu___172_12116.allow_unbound_universes);
                          reify_ = (uu___172_12116.reify_);
                          compress_uvars = (uu___172_12116.compress_uvars);
                          no_full_norm = (uu___172_12116.no_full_norm);
                          check_no_uvars = (uu___172_12116.check_no_uvars);
                          unmeta = (uu___172_12116.unmeta);
                          unascribe = (uu___172_12116.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___172_12116.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12115;
                        tcenv = (uu___171_12114.tcenv);
                        debug = (uu___171_12114.debug);
                        delta_level;
                        primitive_steps = (uu___171_12114.primitive_steps);
                        strong = (uu___171_12114.strong);
                        memoize_lazy = (uu___171_12114.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12125 =
                          let uu____12126 =
                            let uu____12131 = FStar_Util.now ()  in
                            (t1, uu____12131)  in
                          Debug uu____12126  in
                        uu____12125 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12135 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12135
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12144 =
                      let uu____12151 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12151, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12144  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12161 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12161  in
               let uu____12162 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12162
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12168  ->
                       let uu____12169 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12170 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12169 uu____12170);
                  if b
                  then
                    (let uu____12171 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12171 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12179 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12179) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12192),uu____12193);
                                FStar_Syntax_Syntax.sigrng = uu____12194;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12196;
                                FStar_Syntax_Syntax.sigattrs = uu____12197;_},uu____12198),uu____12199)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12264 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___111_12268  ->
                               match uu___111_12268 with
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
                          (let uu____12278 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12278))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12297) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12332,uu____12333) -> false)))
                     in
                  let uu____12350 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12366 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12366 then (true, true) else (false, false)
                     in
                  match uu____12350 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12379  ->
                            let uu____12380 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12381 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12382 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12380 uu____12381 uu____12382);
                       if should_delta2
                       then
                         (let uu____12383 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___173_12399 = cfg  in
                                 {
                                   steps =
                                     (let uu___174_12402 = cfg.steps  in
                                      {
                                        beta = (uu___174_12402.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___174_12402.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___174_12402.unfold_attr);
                                        unfold_tac =
                                          (uu___174_12402.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___174_12402.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___174_12402.erase_universes);
                                        allow_unbound_universes =
                                          (uu___174_12402.allow_unbound_universes);
                                        reify_ = (uu___174_12402.reify_);
                                        compress_uvars =
                                          (uu___174_12402.compress_uvars);
                                        no_full_norm =
                                          (uu___174_12402.no_full_norm);
                                        check_no_uvars =
                                          (uu___174_12402.check_no_uvars);
                                        unmeta = (uu___174_12402.unmeta);
                                        unascribe =
                                          (uu___174_12402.unascribe);
                                        in_full_norm_request =
                                          (uu___174_12402.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___174_12402.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___173_12399.tcenv);
                                   debug = (uu___173_12399.debug);
                                   delta_level = (uu___173_12399.delta_level);
                                   primitive_steps =
                                     (uu___173_12399.primitive_steps);
                                   strong = (uu___173_12399.strong);
                                   memoize_lazy =
                                     (uu___173_12399.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___173_12399.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12383 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12416 = lookup_bvar env x  in
               (match uu____12416 with
                | Univ uu____12417 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12466 = FStar_ST.op_Bang r  in
                      (match uu____12466 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12588  ->
                                 let uu____12589 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12590 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12589
                                   uu____12590);
                            (let uu____12591 = maybe_weakly_reduced t'  in
                             if uu____12591
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12592 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12663)::uu____12664 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12673)::uu____12674 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12686,uu____12687))::stack_rest ->
                    (match c with
                     | Univ uu____12691 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12700 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12721  ->
                                    let uu____12722 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12722);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12762  ->
                                    let uu____12763 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12763);
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
                       (fun uu____12841  ->
                          let uu____12842 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12842);
                     norm cfg env stack1 t1)
                | (Debug uu____12843)::uu____12844 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_12854 = cfg.steps  in
                             {
                               beta = (uu___175_12854.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_12854.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_12854.unfold_until);
                               unfold_only = (uu___175_12854.unfold_only);
                               unfold_fully = (uu___175_12854.unfold_fully);
                               unfold_attr = (uu___175_12854.unfold_attr);
                               unfold_tac = (uu___175_12854.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_12854.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_12854.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_12854.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_12854.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_12854.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_12854.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_12856 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_12856.tcenv);
                               debug = (uu___176_12856.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_12856.primitive_steps);
                               strong = (uu___176_12856.strong);
                               memoize_lazy = (uu___176_12856.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_12856.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12858 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12858 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12900  -> dummy :: env1) env)
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
                                          let uu____12937 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12937)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_12942 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_12942.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_12942.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12943 -> lopt  in
                           (log cfg
                              (fun uu____12949  ->
                                 let uu____12950 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12950);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_12959 = cfg  in
                               {
                                 steps = (uu___178_12959.steps);
                                 tcenv = (uu___178_12959.tcenv);
                                 debug = (uu___178_12959.debug);
                                 delta_level = (uu___178_12959.delta_level);
                                 primitive_steps =
                                   (uu___178_12959.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_12959.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_12959.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12970)::uu____12971 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_12983 = cfg.steps  in
                             {
                               beta = (uu___175_12983.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_12983.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_12983.unfold_until);
                               unfold_only = (uu___175_12983.unfold_only);
                               unfold_fully = (uu___175_12983.unfold_fully);
                               unfold_attr = (uu___175_12983.unfold_attr);
                               unfold_tac = (uu___175_12983.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_12983.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_12983.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_12983.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_12983.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_12983.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_12983.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_12985 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_12985.tcenv);
                               debug = (uu___176_12985.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_12985.primitive_steps);
                               strong = (uu___176_12985.strong);
                               memoize_lazy = (uu___176_12985.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_12985.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12987 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12987 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13029  -> dummy :: env1) env)
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
                                          let uu____13066 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13066)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13071 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13071.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13071.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13072 -> lopt  in
                           (log cfg
                              (fun uu____13078  ->
                                 let uu____13079 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13079);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13088 = cfg  in
                               {
                                 steps = (uu___178_13088.steps);
                                 tcenv = (uu___178_13088.tcenv);
                                 debug = (uu___178_13088.debug);
                                 delta_level = (uu___178_13088.delta_level);
                                 primitive_steps =
                                   (uu___178_13088.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13088.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13088.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13099)::uu____13100 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13114 = cfg.steps  in
                             {
                               beta = (uu___175_13114.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13114.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13114.unfold_until);
                               unfold_only = (uu___175_13114.unfold_only);
                               unfold_fully = (uu___175_13114.unfold_fully);
                               unfold_attr = (uu___175_13114.unfold_attr);
                               unfold_tac = (uu___175_13114.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13114.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13114.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13114.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13114.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13114.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13114.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13116 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13116.tcenv);
                               debug = (uu___176_13116.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13116.primitive_steps);
                               strong = (uu___176_13116.strong);
                               memoize_lazy = (uu___176_13116.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13116.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13118 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13118 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13160  -> dummy :: env1) env)
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
                                          let uu____13197 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13197)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13202 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13202.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13202.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13203 -> lopt  in
                           (log cfg
                              (fun uu____13209  ->
                                 let uu____13210 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13210);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13219 = cfg  in
                               {
                                 steps = (uu___178_13219.steps);
                                 tcenv = (uu___178_13219.tcenv);
                                 debug = (uu___178_13219.debug);
                                 delta_level = (uu___178_13219.delta_level);
                                 primitive_steps =
                                   (uu___178_13219.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13219.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13219.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13230)::uu____13231 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13245 = cfg.steps  in
                             {
                               beta = (uu___175_13245.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13245.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13245.unfold_until);
                               unfold_only = (uu___175_13245.unfold_only);
                               unfold_fully = (uu___175_13245.unfold_fully);
                               unfold_attr = (uu___175_13245.unfold_attr);
                               unfold_tac = (uu___175_13245.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13245.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13245.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13245.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13245.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13245.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13245.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13247 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13247.tcenv);
                               debug = (uu___176_13247.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13247.primitive_steps);
                               strong = (uu___176_13247.strong);
                               memoize_lazy = (uu___176_13247.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13247.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13249 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13249 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13291  -> dummy :: env1) env)
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
                                          let uu____13328 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13328)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13333 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13333.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13333.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13334 -> lopt  in
                           (log cfg
                              (fun uu____13340  ->
                                 let uu____13341 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13341);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13350 = cfg  in
                               {
                                 steps = (uu___178_13350.steps);
                                 tcenv = (uu___178_13350.tcenv);
                                 debug = (uu___178_13350.debug);
                                 delta_level = (uu___178_13350.delta_level);
                                 primitive_steps =
                                   (uu___178_13350.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13350.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13350.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13361)::uu____13362 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13380 = cfg.steps  in
                             {
                               beta = (uu___175_13380.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13380.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13380.unfold_until);
                               unfold_only = (uu___175_13380.unfold_only);
                               unfold_fully = (uu___175_13380.unfold_fully);
                               unfold_attr = (uu___175_13380.unfold_attr);
                               unfold_tac = (uu___175_13380.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13380.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13380.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13380.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13380.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13380.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13380.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13382 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13382.tcenv);
                               debug = (uu___176_13382.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13382.primitive_steps);
                               strong = (uu___176_13382.strong);
                               memoize_lazy = (uu___176_13382.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13382.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13384 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13384 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13426  -> dummy :: env1) env)
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
                                          let uu____13463 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13463)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13468 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13468.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13468.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13469 -> lopt  in
                           (log cfg
                              (fun uu____13475  ->
                                 let uu____13476 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13476);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13485 = cfg  in
                               {
                                 steps = (uu___178_13485.steps);
                                 tcenv = (uu___178_13485.tcenv);
                                 debug = (uu___178_13485.debug);
                                 delta_level = (uu___178_13485.delta_level);
                                 primitive_steps =
                                   (uu___178_13485.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13485.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13485.normalize_pure_lets)
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
                             let uu___175_13499 = cfg.steps  in
                             {
                               beta = (uu___175_13499.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13499.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13499.unfold_until);
                               unfold_only = (uu___175_13499.unfold_only);
                               unfold_fully = (uu___175_13499.unfold_fully);
                               unfold_attr = (uu___175_13499.unfold_attr);
                               unfold_tac = (uu___175_13499.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13499.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13499.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13499.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13499.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13499.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13499.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13501 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13501.tcenv);
                               debug = (uu___176_13501.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13501.primitive_steps);
                               strong = (uu___176_13501.strong);
                               memoize_lazy = (uu___176_13501.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13501.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13503 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13503 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13545  -> dummy :: env1) env)
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
                                          let uu____13582 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13582)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13587 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13587.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13587.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13588 -> lopt  in
                           (log cfg
                              (fun uu____13594  ->
                                 let uu____13595 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13595);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13604 = cfg  in
                               {
                                 steps = (uu___178_13604.steps);
                                 tcenv = (uu___178_13604.tcenv);
                                 debug = (uu___178_13604.debug);
                                 delta_level = (uu___178_13604.delta_level);
                                 primitive_steps =
                                   (uu___178_13604.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13604.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13604.normalize_pure_lets)
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
                      (fun uu____13653  ->
                         fun stack1  ->
                           match uu____13653 with
                           | (a,aq) ->
                               let uu____13665 =
                                 let uu____13666 =
                                   let uu____13673 =
                                     let uu____13674 =
                                       let uu____13705 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13705, false)  in
                                     Clos uu____13674  in
                                   (uu____13673, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13666  in
                               uu____13665 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13789  ->
                     let uu____13790 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13790);
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
                             ((let uu___179_13826 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___179_13826.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___179_13826.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13827 ->
                      let uu____13832 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13832)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13835 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13835 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13866 =
                          let uu____13867 =
                            let uu____13874 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___180_13876 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___180_13876.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___180_13876.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13874)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13867  in
                        mk uu____13866 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13895 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13895
               else
                 (let uu____13897 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13897 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13905 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13929  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13905 c1  in
                      let t2 =
                        let uu____13951 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13951 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14062)::uu____14063 ->
                    (log cfg
                       (fun uu____14076  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14077)::uu____14078 ->
                    (log cfg
                       (fun uu____14089  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14090,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14091;
                                   FStar_Syntax_Syntax.vars = uu____14092;_},uu____14093,uu____14094))::uu____14095
                    ->
                    (log cfg
                       (fun uu____14104  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14105)::uu____14106 ->
                    (log cfg
                       (fun uu____14117  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14118 ->
                    (log cfg
                       (fun uu____14121  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14125  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14142 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14142
                         | FStar_Util.Inr c ->
                             let uu____14150 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14150
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14163 =
                               let uu____14164 =
                                 let uu____14191 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14191, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14164
                                in
                             mk uu____14163 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14210 ->
                           let uu____14211 =
                             let uu____14212 =
                               let uu____14213 =
                                 let uu____14240 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14240, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14213
                                in
                             mk uu____14212 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14211))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___181_14317 = cfg  in
                   {
                     steps =
                       (let uu___182_14320 = cfg.steps  in
                        {
                          beta = (uu___182_14320.beta);
                          iota = (uu___182_14320.iota);
                          zeta = (uu___182_14320.zeta);
                          weak = true;
                          hnf = (uu___182_14320.hnf);
                          primops = (uu___182_14320.primops);
                          do_not_unfold_pure_lets =
                            (uu___182_14320.do_not_unfold_pure_lets);
                          unfold_until = (uu___182_14320.unfold_until);
                          unfold_only = (uu___182_14320.unfold_only);
                          unfold_fully = (uu___182_14320.unfold_fully);
                          unfold_attr = (uu___182_14320.unfold_attr);
                          unfold_tac = (uu___182_14320.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___182_14320.pure_subterms_within_computations);
                          simplify = (uu___182_14320.simplify);
                          erase_universes = (uu___182_14320.erase_universes);
                          allow_unbound_universes =
                            (uu___182_14320.allow_unbound_universes);
                          reify_ = (uu___182_14320.reify_);
                          compress_uvars = (uu___182_14320.compress_uvars);
                          no_full_norm = (uu___182_14320.no_full_norm);
                          check_no_uvars = (uu___182_14320.check_no_uvars);
                          unmeta = (uu___182_14320.unmeta);
                          unascribe = (uu___182_14320.unascribe);
                          in_full_norm_request =
                            (uu___182_14320.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___182_14320.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___181_14317.tcenv);
                     debug = (uu___181_14317.debug);
                     delta_level = (uu___181_14317.delta_level);
                     primitive_steps = (uu___181_14317.primitive_steps);
                     strong = (uu___181_14317.strong);
                     memoize_lazy = (uu___181_14317.memoize_lazy);
                     normalize_pure_lets =
                       (uu___181_14317.normalize_pure_lets)
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
                         let uu____14356 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14356 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___183_14376 = cfg  in
                               let uu____14377 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___183_14376.steps);
                                 tcenv = uu____14377;
                                 debug = (uu___183_14376.debug);
                                 delta_level = (uu___183_14376.delta_level);
                                 primitive_steps =
                                   (uu___183_14376.primitive_steps);
                                 strong = (uu___183_14376.strong);
                                 memoize_lazy = (uu___183_14376.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14376.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14384 =
                                 let uu____14385 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14385  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14384
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___184_14388 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___184_14388.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___184_14388.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___184_14388.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___184_14388.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14389 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14389
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14400,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14401;
                               FStar_Syntax_Syntax.lbunivs = uu____14402;
                               FStar_Syntax_Syntax.lbtyp = uu____14403;
                               FStar_Syntax_Syntax.lbeff = uu____14404;
                               FStar_Syntax_Syntax.lbdef = uu____14405;
                               FStar_Syntax_Syntax.lbattrs = uu____14406;
                               FStar_Syntax_Syntax.lbpos = uu____14407;_}::uu____14408),uu____14409)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14449 =
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
               if uu____14449
               then
                 let binder =
                   let uu____14451 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14451  in
                 let env1 =
                   let uu____14461 =
                     let uu____14468 =
                       let uu____14469 =
                         let uu____14500 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14500,
                           false)
                          in
                       Clos uu____14469  in
                     ((FStar_Pervasives_Native.Some binder), uu____14468)  in
                   uu____14461 :: env  in
                 (log cfg
                    (fun uu____14593  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14597  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14598 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14598))
                 else
                   (let uu____14600 =
                      let uu____14605 =
                        let uu____14606 =
                          let uu____14607 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14607
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14606]  in
                      FStar_Syntax_Subst.open_term uu____14605 body  in
                    match uu____14600 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14616  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14624 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14624  in
                            FStar_Util.Inl
                              (let uu___185_14634 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___185_14634.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___185_14634.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14637  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___186_14639 = lb  in
                             let uu____14640 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___186_14639.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___186_14639.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14640;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___186_14639.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___186_14639.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14675  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___187_14698 = cfg  in
                             {
                               steps = (uu___187_14698.steps);
                               tcenv = (uu___187_14698.tcenv);
                               debug = (uu___187_14698.debug);
                               delta_level = (uu___187_14698.delta_level);
                               primitive_steps =
                                 (uu___187_14698.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___187_14698.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___187_14698.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14701  ->
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
               let uu____14718 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14718 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14754 =
                               let uu___188_14755 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___188_14755.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___188_14755.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14754  in
                           let uu____14756 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14756 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14782 =
                                   FStar_List.map (fun uu____14798  -> dummy)
                                     lbs1
                                    in
                                 let uu____14799 =
                                   let uu____14808 =
                                     FStar_List.map
                                       (fun uu____14828  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14808 env  in
                                 FStar_List.append uu____14782 uu____14799
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14852 =
                                       let uu___189_14853 = rc  in
                                       let uu____14854 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___189_14853.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14854;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___189_14853.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14852
                                 | uu____14861 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___190_14865 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___190_14865.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___190_14865.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___190_14865.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___190_14865.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14875 =
                        FStar_List.map (fun uu____14891  -> dummy) lbs2  in
                      FStar_List.append uu____14875 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14899 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14899 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___191_14915 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___191_14915.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___191_14915.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____14942 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14942
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14961 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15037  ->
                        match uu____15037 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___192_15158 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___192_15158.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___192_15158.FStar_Syntax_Syntax.sort)
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
               (match uu____14961 with
                | (rec_env,memos,uu____15371) ->
                    let uu____15424 =
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
                             let uu____15747 =
                               let uu____15754 =
                                 let uu____15755 =
                                   let uu____15786 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15786, false)
                                    in
                                 Clos uu____15755  in
                               (FStar_Pervasives_Native.None, uu____15754)
                                in
                             uu____15747 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15896  ->
                     let uu____15897 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15897);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15919 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15921::uu____15922 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15927) ->
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
                             | uu____15950 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15964 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15964
                              | uu____15975 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15979 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16005 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16023 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16040 =
                        let uu____16041 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16042 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16041 uu____16042
                         in
                      failwith uu____16040
                    else rebuild cfg env stack t2
                | uu____16044 -> norm cfg env stack t2))

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
                let uu____16054 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16054  in
              let uu____16055 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16055 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16068  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16079  ->
                        let uu____16080 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16081 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16080 uu____16081);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16086 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16086 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16095))::stack1 ->
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
                      | uu____16150 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16153 ->
                          let uu____16156 =
                            let uu____16157 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16157
                             in
                          failwith uu____16156
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
                  let uu___193_16181 = cfg  in
                  let uu____16182 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16182;
                    tcenv = (uu___193_16181.tcenv);
                    debug = (uu___193_16181.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___193_16181.primitive_steps);
                    strong = (uu___193_16181.strong);
                    memoize_lazy = (uu___193_16181.memoize_lazy);
                    normalize_pure_lets =
                      (uu___193_16181.normalize_pure_lets)
                  }
                else
                  (let uu___194_16184 = cfg  in
                   {
                     steps =
                       (let uu___195_16187 = cfg.steps  in
                        {
                          beta = (uu___195_16187.beta);
                          iota = (uu___195_16187.iota);
                          zeta = false;
                          weak = (uu___195_16187.weak);
                          hnf = (uu___195_16187.hnf);
                          primops = (uu___195_16187.primops);
                          do_not_unfold_pure_lets =
                            (uu___195_16187.do_not_unfold_pure_lets);
                          unfold_until = (uu___195_16187.unfold_until);
                          unfold_only = (uu___195_16187.unfold_only);
                          unfold_fully = (uu___195_16187.unfold_fully);
                          unfold_attr = (uu___195_16187.unfold_attr);
                          unfold_tac = (uu___195_16187.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___195_16187.pure_subterms_within_computations);
                          simplify = (uu___195_16187.simplify);
                          erase_universes = (uu___195_16187.erase_universes);
                          allow_unbound_universes =
                            (uu___195_16187.allow_unbound_universes);
                          reify_ = (uu___195_16187.reify_);
                          compress_uvars = (uu___195_16187.compress_uvars);
                          no_full_norm = (uu___195_16187.no_full_norm);
                          check_no_uvars = (uu___195_16187.check_no_uvars);
                          unmeta = (uu___195_16187.unmeta);
                          unascribe = (uu___195_16187.unascribe);
                          in_full_norm_request =
                            (uu___195_16187.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___195_16187.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___194_16184.tcenv);
                     debug = (uu___194_16184.debug);
                     delta_level = (uu___194_16184.delta_level);
                     primitive_steps = (uu___194_16184.primitive_steps);
                     strong = (uu___194_16184.strong);
                     memoize_lazy = (uu___194_16184.memoize_lazy);
                     normalize_pure_lets =
                       (uu___194_16184.normalize_pure_lets)
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
                  (fun uu____16217  ->
                     let uu____16218 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16219 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16218
                       uu____16219);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16221 =
                   let uu____16222 = FStar_Syntax_Subst.compress head3  in
                   uu____16222.FStar_Syntax_Syntax.n  in
                 match uu____16221 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16240 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16240
                        in
                     let uu____16241 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16241 with
                      | (uu____16242,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16248 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16258 =
                                   let uu____16259 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16259.FStar_Syntax_Syntax.n  in
                                 match uu____16258 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16265,uu____16266))
                                     ->
                                     let uu____16275 =
                                       let uu____16276 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16276.FStar_Syntax_Syntax.n  in
                                     (match uu____16275 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16282,msrc,uu____16284))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16293 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16293
                                      | uu____16294 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16295 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16296 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16296 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___196_16301 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___196_16301.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___196_16301.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___196_16301.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___196_16301.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___196_16301.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16302 = FStar_List.tl stack  in
                                    let uu____16303 =
                                      let uu____16304 =
                                        let uu____16311 =
                                          let uu____16312 =
                                            let uu____16325 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16325)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16312
                                           in
                                        FStar_Syntax_Syntax.mk uu____16311
                                         in
                                      uu____16304
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16302 uu____16303
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16341 =
                                      let uu____16342 = is_return body  in
                                      match uu____16342 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16346;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16347;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16352 -> false  in
                                    if uu____16341
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
                                         let uu____16375 =
                                           let uu____16382 =
                                             let uu____16383 =
                                               let uu____16400 =
                                                 let uu____16403 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16403]  in
                                               (uu____16400, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16383
                                              in
                                           FStar_Syntax_Syntax.mk uu____16382
                                            in
                                         uu____16375
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16421 =
                                           let uu____16422 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16422.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16421 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16428::uu____16429::[])
                                             ->
                                             let uu____16436 =
                                               let uu____16443 =
                                                 let uu____16444 =
                                                   let uu____16451 =
                                                     let uu____16454 =
                                                       let uu____16455 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16455
                                                        in
                                                     let uu____16456 =
                                                       let uu____16459 =
                                                         let uu____16460 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16460
                                                          in
                                                       [uu____16459]  in
                                                     uu____16454 ::
                                                       uu____16456
                                                      in
                                                   (bind1, uu____16451)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16444
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16443
                                                in
                                             uu____16436
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16468 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16474 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16474
                                         then
                                           let uu____16477 =
                                             let uu____16478 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16478
                                              in
                                           let uu____16479 =
                                             let uu____16482 =
                                               let uu____16483 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16483
                                                in
                                             [uu____16482]  in
                                           uu____16477 :: uu____16479
                                         else []  in
                                       let reified =
                                         let uu____16488 =
                                           let uu____16495 =
                                             let uu____16496 =
                                               let uu____16511 =
                                                 let uu____16514 =
                                                   let uu____16517 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16518 =
                                                     let uu____16521 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16521]  in
                                                   uu____16517 :: uu____16518
                                                    in
                                                 let uu____16522 =
                                                   let uu____16525 =
                                                     let uu____16528 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16529 =
                                                       let uu____16532 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16533 =
                                                         let uu____16536 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16537 =
                                                           let uu____16540 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16540]  in
                                                         uu____16536 ::
                                                           uu____16537
                                                          in
                                                       uu____16532 ::
                                                         uu____16533
                                                        in
                                                     uu____16528 ::
                                                       uu____16529
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16525
                                                    in
                                                 FStar_List.append
                                                   uu____16514 uu____16522
                                                  in
                                               (bind_inst, uu____16511)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16496
                                              in
                                           FStar_Syntax_Syntax.mk uu____16495
                                            in
                                         uu____16488
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16552  ->
                                            let uu____16553 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16554 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16553 uu____16554);
                                       (let uu____16555 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16555 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16579 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16579
                        in
                     let uu____16580 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16580 with
                      | (uu____16581,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16620 =
                                  let uu____16621 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16621.FStar_Syntax_Syntax.n  in
                                match uu____16620 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16627) -> t2
                                | uu____16632 -> head4  in
                              let uu____16633 =
                                let uu____16634 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16634.FStar_Syntax_Syntax.n  in
                              match uu____16633 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16640 -> FStar_Pervasives_Native.None
                               in
                            let uu____16641 = maybe_extract_fv head4  in
                            match uu____16641 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16651 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16651
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16656 = maybe_extract_fv head5
                                     in
                                  match uu____16656 with
                                  | FStar_Pervasives_Native.Some uu____16661
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16662 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16667 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16684 =
                              match uu____16684 with
                              | (e,q) ->
                                  let uu____16691 =
                                    let uu____16692 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16692.FStar_Syntax_Syntax.n  in
                                  (match uu____16691 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16707 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16707
                                   | uu____16708 -> false)
                               in
                            let uu____16709 =
                              let uu____16710 =
                                let uu____16717 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16717 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16710
                               in
                            if uu____16709
                            then
                              let uu____16722 =
                                let uu____16723 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16723
                                 in
                              failwith uu____16722
                            else ());
                           (let uu____16725 = maybe_unfold_action head_app
                               in
                            match uu____16725 with
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
                                   (fun uu____16768  ->
                                      let uu____16769 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16770 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16769 uu____16770);
                                 (let uu____16771 = FStar_List.tl stack  in
                                  norm cfg env uu____16771 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16773) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16797 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16797  in
                     (log cfg
                        (fun uu____16801  ->
                           let uu____16802 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16802);
                      (let uu____16803 = FStar_List.tl stack  in
                       norm cfg env uu____16803 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16924  ->
                               match uu____16924 with
                               | (pat,wopt,tm) ->
                                   let uu____16972 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____16972)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17004 = FStar_List.tl stack  in
                     norm cfg env uu____17004 tm
                 | uu____17005 -> fallback ())

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
              (fun uu____17019  ->
                 let uu____17020 = FStar_Ident.string_of_lid msrc  in
                 let uu____17021 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17022 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17020
                   uu____17021 uu____17022);
            (let uu____17023 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17023
             then
               let ed =
                 let uu____17025 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17025  in
               let uu____17026 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17026 with
               | (uu____17027,return_repr) ->
                   let return_inst =
                     let uu____17036 =
                       let uu____17037 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17037.FStar_Syntax_Syntax.n  in
                     match uu____17036 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17043::[]) ->
                         let uu____17050 =
                           let uu____17057 =
                             let uu____17058 =
                               let uu____17065 =
                                 let uu____17068 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17068]  in
                               (return_tm, uu____17065)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17058  in
                           FStar_Syntax_Syntax.mk uu____17057  in
                         uu____17050 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17076 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17079 =
                     let uu____17086 =
                       let uu____17087 =
                         let uu____17102 =
                           let uu____17105 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17106 =
                             let uu____17109 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17109]  in
                           uu____17105 :: uu____17106  in
                         (return_inst, uu____17102)  in
                       FStar_Syntax_Syntax.Tm_app uu____17087  in
                     FStar_Syntax_Syntax.mk uu____17086  in
                   uu____17079 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17118 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17118 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17121 =
                      let uu____17122 = FStar_Ident.text_of_lid msrc  in
                      let uu____17123 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17122 uu____17123
                       in
                    failwith uu____17121
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17124;
                      FStar_TypeChecker_Env.mtarget = uu____17125;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17126;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17148 =
                      let uu____17149 = FStar_Ident.text_of_lid msrc  in
                      let uu____17150 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17149 uu____17150
                       in
                    failwith uu____17148
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17151;
                      FStar_TypeChecker_Env.mtarget = uu____17152;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17153;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17188 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17189 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17188 t FStar_Syntax_Syntax.tun uu____17189))

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
                (fun uu____17245  ->
                   match uu____17245 with
                   | (a,imp) ->
                       let uu____17256 = norm cfg env [] a  in
                       (uu____17256, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17264  ->
             let uu____17265 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17266 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17265 uu____17266);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17290 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17290
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___197_17293 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___197_17293.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___197_17293.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17313 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17313
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___198_17316 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___198_17316.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___198_17316.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17351  ->
                      match uu____17351 with
                      | (a,i) ->
                          let uu____17362 = norm cfg env [] a  in
                          (uu____17362, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___112_17380  ->
                       match uu___112_17380 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17384 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17384
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___199_17392 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___200_17395 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___200_17395.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___199_17392.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___199_17392.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17398  ->
        match uu____17398 with
        | (x,imp) ->
            let uu____17401 =
              let uu___201_17402 = x  in
              let uu____17403 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___201_17402.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___201_17402.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17403
              }  in
            (uu____17401, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17409 =
          FStar_List.fold_left
            (fun uu____17427  ->
               fun b  ->
                 match uu____17427 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17409 with | (nbs,uu____17467) -> FStar_List.rev nbs

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
            let uu____17483 =
              let uu___202_17484 = rc  in
              let uu____17485 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___202_17484.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17485;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___202_17484.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17483
        | uu____17492 -> lopt

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
            (let uu____17513 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17514 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17513
               uu____17514)
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
          let uu____17534 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17534
          then tm1
          else
            (let w t =
               let uu___203_17548 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___203_17548.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___203_17548.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17559 =
                 let uu____17560 = FStar_Syntax_Util.unmeta t  in
                 uu____17560.FStar_Syntax_Syntax.n  in
               match uu____17559 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17567 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17616)::args1,(bv,uu____17619)::bs1) ->
                   let uu____17653 =
                     let uu____17654 = FStar_Syntax_Subst.compress t  in
                     uu____17654.FStar_Syntax_Syntax.n  in
                   (match uu____17653 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17658 -> false)
               | ([],[]) -> true
               | (uu____17679,uu____17680) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17721 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17722 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17721
                    uu____17722)
               else ();
               (let uu____17724 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17724 with
                | (hd1,args) ->
                    let uu____17757 =
                      let uu____17758 = FStar_Syntax_Subst.compress hd1  in
                      uu____17758.FStar_Syntax_Syntax.n  in
                    (match uu____17757 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____17765 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17766 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17767 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17765 uu____17766 uu____17767)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17769 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17786 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17787 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17786
                    uu____17787)
               else ();
               (let uu____17789 = FStar_Syntax_Util.is_squash t  in
                match uu____17789 with
                | FStar_Pervasives_Native.Some (uu____17800,t') ->
                    is_applied bs t'
                | uu____17812 ->
                    let uu____17821 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17821 with
                     | FStar_Pervasives_Native.Some (uu____17832,t') ->
                         is_applied bs t'
                     | uu____17844 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17868 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17868 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17875)::(q,uu____17877)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____17913 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17914 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17913 uu____17914)
                    else ();
                    (let uu____17916 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17916 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17921 =
                           let uu____17922 = FStar_Syntax_Subst.compress p
                              in
                           uu____17922.FStar_Syntax_Syntax.n  in
                         (match uu____17921 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17930 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17930))
                          | uu____17931 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17934)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17959 =
                           let uu____17960 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17960.FStar_Syntax_Syntax.n  in
                         (match uu____17959 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17968 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17968))
                          | uu____17969 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17973 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17973 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17978 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17978 with
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
                                     let uu____17987 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17987))
                               | uu____17988 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17993)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18018 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18018 with
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
                                     let uu____18027 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18027))
                               | uu____18028 -> FStar_Pervasives_Native.None)
                          | uu____18031 -> FStar_Pervasives_Native.None)
                     | uu____18034 -> FStar_Pervasives_Native.None))
               | uu____18037 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18050 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18050 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18056)::[],uu____18057,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18074 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18075 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18074
                         uu____18075)
                    else ();
                    is_quantified_const bv phi')
               | uu____18077 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18090 =
                 let uu____18091 = FStar_Syntax_Subst.compress phi  in
                 uu____18091.FStar_Syntax_Syntax.n  in
               match uu____18090 with
               | FStar_Syntax_Syntax.Tm_match (uu____18096,br::brs) ->
                   let uu____18163 = br  in
                   (match uu____18163 with
                    | (uu____18180,uu____18181,e) ->
                        let r =
                          let uu____18202 = simp_t e  in
                          match uu____18202 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18208 =
                                FStar_List.for_all
                                  (fun uu____18226  ->
                                     match uu____18226 with
                                     | (uu____18239,uu____18240,e') ->
                                         let uu____18254 = simp_t e'  in
                                         uu____18254 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18208
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18262 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18269 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18269
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18294 =
                 match uu____18294 with
                 | (t1,q) ->
                     let uu____18307 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18307 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18335 -> (t1, q))
                  in
               let uu____18344 = FStar_Syntax_Util.head_and_args t  in
               match uu____18344 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18408 =
                 let uu____18409 = FStar_Syntax_Util.unmeta ty  in
                 uu____18409.FStar_Syntax_Syntax.n  in
               match uu____18408 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18413) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18418,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18438 -> false  in
             let simplify1 arg =
               let uu____18463 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18463, arg)  in
             let uu____18472 = is_forall_const tm1  in
             match uu____18472 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____18477 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18478 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18477
                       uu____18478)
                  else ();
                  (let uu____18480 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18480))
             | FStar_Pervasives_Native.None  ->
                 let uu____18481 =
                   let uu____18482 = FStar_Syntax_Subst.compress tm1  in
                   uu____18482.FStar_Syntax_Syntax.n  in
                 (match uu____18481 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18486;
                              FStar_Syntax_Syntax.vars = uu____18487;_},uu____18488);
                         FStar_Syntax_Syntax.pos = uu____18489;
                         FStar_Syntax_Syntax.vars = uu____18490;_},args)
                      ->
                      let uu____18516 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18516
                      then
                        let uu____18517 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18517 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18564)::
                             (uu____18565,(arg,uu____18567))::[] ->
                             maybe_auto_squash arg
                         | (uu____18616,(arg,uu____18618))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18619)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18668)::uu____18669::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18720::(FStar_Pervasives_Native.Some (false
                                         ),uu____18721)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18772 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18786 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18786
                         then
                           let uu____18787 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18787 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18834)::uu____18835::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18886::(FStar_Pervasives_Native.Some (true
                                           ),uu____18887)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18938)::(uu____18939,(arg,uu____18941))::[]
                               -> maybe_auto_squash arg
                           | (uu____18990,(arg,uu____18992))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18993)::[]
                               -> maybe_auto_squash arg
                           | uu____19042 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19056 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19056
                            then
                              let uu____19057 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19057 with
                              | uu____19104::(FStar_Pervasives_Native.Some
                                              (true ),uu____19105)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19156)::uu____19157::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19208)::(uu____19209,(arg,uu____19211))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19260,(p,uu____19262))::(uu____19263,
                                                                (q,uu____19265))::[]
                                  ->
                                  let uu____19312 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19312
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19314 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19328 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19328
                               then
                                 let uu____19329 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19329 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19376)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19377)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19428)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19429)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19480)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19481)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19532)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19533)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19584,(arg,uu____19586))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19587)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19636)::(uu____19637,(arg,uu____19639))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19688,(arg,uu____19690))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19691)::[]
                                     ->
                                     let uu____19740 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19740
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19741)::(uu____19742,(arg,uu____19744))::[]
                                     ->
                                     let uu____19793 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19793
                                 | (uu____19794,(p,uu____19796))::(uu____19797,
                                                                   (q,uu____19799))::[]
                                     ->
                                     let uu____19846 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19846
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19848 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19862 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19862
                                  then
                                    let uu____19863 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19863 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19910)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19941)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19972 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19986 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19986
                                     then
                                       match args with
                                       | (t,uu____19988)::[] ->
                                           let uu____20005 =
                                             let uu____20006 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20006.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20005 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20009::[],body,uu____20011)
                                                ->
                                                let uu____20038 = simp_t body
                                                   in
                                                (match uu____20038 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20041 -> tm1)
                                            | uu____20044 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20046))::(t,uu____20048)::[]
                                           ->
                                           let uu____20087 =
                                             let uu____20088 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20088.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20087 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20091::[],body,uu____20093)
                                                ->
                                                let uu____20120 = simp_t body
                                                   in
                                                (match uu____20120 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20123 -> tm1)
                                            | uu____20126 -> tm1)
                                       | uu____20127 -> tm1
                                     else
                                       (let uu____20137 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20137
                                        then
                                          match args with
                                          | (t,uu____20139)::[] ->
                                              let uu____20156 =
                                                let uu____20157 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20157.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20156 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20160::[],body,uu____20162)
                                                   ->
                                                   let uu____20189 =
                                                     simp_t body  in
                                                   (match uu____20189 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20192 -> tm1)
                                               | uu____20195 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20197))::(t,uu____20199)::[]
                                              ->
                                              let uu____20238 =
                                                let uu____20239 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20239.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20238 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20242::[],body,uu____20244)
                                                   ->
                                                   let uu____20271 =
                                                     simp_t body  in
                                                   (match uu____20271 with
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
                                                    | uu____20274 -> tm1)
                                               | uu____20277 -> tm1)
                                          | uu____20278 -> tm1
                                        else
                                          (let uu____20288 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20288
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20289;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20290;_},uu____20291)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20308;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20309;_},uu____20310)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20327 -> tm1
                                           else
                                             (let uu____20337 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20337 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20357 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20367;
                         FStar_Syntax_Syntax.vars = uu____20368;_},args)
                      ->
                      let uu____20390 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20390
                      then
                        let uu____20391 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20391 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20438)::
                             (uu____20439,(arg,uu____20441))::[] ->
                             maybe_auto_squash arg
                         | (uu____20490,(arg,uu____20492))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20493)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20542)::uu____20543::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20594::(FStar_Pervasives_Native.Some (false
                                         ),uu____20595)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20646 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20660 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20660
                         then
                           let uu____20661 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20661 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20708)::uu____20709::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20760::(FStar_Pervasives_Native.Some (true
                                           ),uu____20761)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20812)::(uu____20813,(arg,uu____20815))::[]
                               -> maybe_auto_squash arg
                           | (uu____20864,(arg,uu____20866))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20867)::[]
                               -> maybe_auto_squash arg
                           | uu____20916 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20930 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20930
                            then
                              let uu____20931 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20931 with
                              | uu____20978::(FStar_Pervasives_Native.Some
                                              (true ),uu____20979)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21030)::uu____21031::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21082)::(uu____21083,(arg,uu____21085))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21134,(p,uu____21136))::(uu____21137,
                                                                (q,uu____21139))::[]
                                  ->
                                  let uu____21186 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21186
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21188 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21202 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21202
                               then
                                 let uu____21203 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21203 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21250)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21251)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21302)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21303)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21354)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21355)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21406)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21407)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21458,(arg,uu____21460))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21461)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21510)::(uu____21511,(arg,uu____21513))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21562,(arg,uu____21564))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21565)::[]
                                     ->
                                     let uu____21614 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21614
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21615)::(uu____21616,(arg,uu____21618))::[]
                                     ->
                                     let uu____21667 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21667
                                 | (uu____21668,(p,uu____21670))::(uu____21671,
                                                                   (q,uu____21673))::[]
                                     ->
                                     let uu____21720 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21720
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21722 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21736 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21736
                                  then
                                    let uu____21737 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21737 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21784)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21815)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21846 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21860 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21860
                                     then
                                       match args with
                                       | (t,uu____21862)::[] ->
                                           let uu____21879 =
                                             let uu____21880 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21880.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21879 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21883::[],body,uu____21885)
                                                ->
                                                let uu____21912 = simp_t body
                                                   in
                                                (match uu____21912 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21915 -> tm1)
                                            | uu____21918 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21920))::(t,uu____21922)::[]
                                           ->
                                           let uu____21961 =
                                             let uu____21962 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21962.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21961 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21965::[],body,uu____21967)
                                                ->
                                                let uu____21994 = simp_t body
                                                   in
                                                (match uu____21994 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21997 -> tm1)
                                            | uu____22000 -> tm1)
                                       | uu____22001 -> tm1
                                     else
                                       (let uu____22011 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22011
                                        then
                                          match args with
                                          | (t,uu____22013)::[] ->
                                              let uu____22030 =
                                                let uu____22031 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22031.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22030 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22034::[],body,uu____22036)
                                                   ->
                                                   let uu____22063 =
                                                     simp_t body  in
                                                   (match uu____22063 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22066 -> tm1)
                                               | uu____22069 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22071))::(t,uu____22073)::[]
                                              ->
                                              let uu____22112 =
                                                let uu____22113 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22113.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22112 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22116::[],body,uu____22118)
                                                   ->
                                                   let uu____22145 =
                                                     simp_t body  in
                                                   (match uu____22145 with
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
                                                    | uu____22148 -> tm1)
                                               | uu____22151 -> tm1)
                                          | uu____22152 -> tm1
                                        else
                                          (let uu____22162 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22162
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22163;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22164;_},uu____22165)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22182;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22183;_},uu____22184)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22201 -> tm1
                                           else
                                             (let uu____22211 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22211 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22231 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22246 = simp_t t  in
                      (match uu____22246 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22249 ->
                      let uu____22272 = is_const_match tm1  in
                      (match uu____22272 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22275 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22285  ->
               (let uu____22287 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22288 = FStar_Syntax_Print.term_to_string t  in
                let uu____22289 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22296 =
                  let uu____22297 =
                    let uu____22300 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22300
                     in
                  stack_to_string uu____22297  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22287 uu____22288 uu____22289 uu____22296);
               (let uu____22323 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22323
                then
                  let uu____22324 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22324 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22331 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22332 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22333 =
                          let uu____22334 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22334
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22331
                          uu____22332 uu____22333);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22352 =
                     let uu____22353 =
                       let uu____22354 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22354  in
                     FStar_Util.string_of_int uu____22353  in
                   let uu____22359 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22360 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22352 uu____22359 uu____22360)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22366,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22415  ->
                     let uu____22416 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22416);
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
               let uu____22452 =
                 let uu___204_22453 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___204_22453.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___204_22453.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22452
           | (Arg (Univ uu____22454,uu____22455,uu____22456))::uu____22457 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22460,uu____22461))::uu____22462 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22477,uu____22478),aq,r))::stack1
               when
               let uu____22528 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22528 ->
               let t2 =
                 let uu____22532 =
                   let uu____22537 =
                     let uu____22538 = closure_as_term cfg env_arg tm  in
                     (uu____22538, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22537  in
                 uu____22532 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22544),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22597  ->
                     let uu____22598 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22598);
                (let should_norm_arg =
                   (Prims.op_Negation (cfg.steps).hnf) ||
                     ((cfg.steps).primops && (is_primop_app cfg t1))
                    in
                 if Prims.op_Negation (cfg.steps).iota
                 then
                   (if should_norm_arg
                    then
                      let stack2 = (App (env, t1, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm
                    else
                      (let arg = closure_as_term cfg env_arg tm  in
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
                 else
                   (let uu____22609 = FStar_ST.op_Bang m  in
                    match uu____22609 with
                    | FStar_Pervasives_Native.None  ->
                        if should_norm_arg
                        then
                          let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm
                        else
                          (let arg = closure_as_term cfg env_arg tm  in
                           let t2 =
                             FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                               FStar_Pervasives_Native.None r
                              in
                           rebuild cfg env_arg stack1 t2)
                    | FStar_Pervasives_Native.Some (uu____22750,a) ->
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (a, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env_arg stack1 t2)))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22801 =
                 log cfg
                   (fun uu____22805  ->
                      let uu____22806 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22806);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22810 =
                 let uu____22811 = FStar_Syntax_Subst.compress t1  in
                 uu____22811.FStar_Syntax_Syntax.n  in
               (match uu____22810 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22838 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22838  in
                    (log cfg
                       (fun uu____22842  ->
                          let uu____22843 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22843);
                     (let uu____22844 = FStar_List.tl stack  in
                      norm cfg env1 uu____22844 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22845);
                       FStar_Syntax_Syntax.pos = uu____22846;
                       FStar_Syntax_Syntax.vars = uu____22847;_},(e,uu____22849)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22878 when
                    (cfg.steps).primops ->
                    let uu____22893 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22893 with
                     | (hd1,args) ->
                         let uu____22930 =
                           let uu____22931 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____22931.FStar_Syntax_Syntax.n  in
                         (match uu____22930 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____22935 = find_prim_step cfg fv  in
                              (match uu____22935 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____22938; arity = uu____22939;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____22941;
                                     requires_binder_substitution =
                                       uu____22942;
                                     interpretation = uu____22943;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____22958 -> fallback " (3)" ())
                          | uu____22961 -> fallback " (4)" ()))
                | uu____22962 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____22983  ->
                     let uu____22984 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22984);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____22993 =
                   log cfg1
                     (fun uu____22998  ->
                        let uu____22999 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23000 =
                          let uu____23001 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23018  ->
                                    match uu____23018 with
                                    | (p,uu____23028,uu____23029) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23001
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____22999 uu____23000);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___113_23046  ->
                                match uu___113_23046 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23047 -> false))
                         in
                      let steps =
                        let uu___205_23049 = cfg1.steps  in
                        {
                          beta = (uu___205_23049.beta);
                          iota = (uu___205_23049.iota);
                          zeta = false;
                          weak = (uu___205_23049.weak);
                          hnf = (uu___205_23049.hnf);
                          primops = (uu___205_23049.primops);
                          do_not_unfold_pure_lets =
                            (uu___205_23049.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___205_23049.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___205_23049.pure_subterms_within_computations);
                          simplify = (uu___205_23049.simplify);
                          erase_universes = (uu___205_23049.erase_universes);
                          allow_unbound_universes =
                            (uu___205_23049.allow_unbound_universes);
                          reify_ = (uu___205_23049.reify_);
                          compress_uvars = (uu___205_23049.compress_uvars);
                          no_full_norm = (uu___205_23049.no_full_norm);
                          check_no_uvars = (uu___205_23049.check_no_uvars);
                          unmeta = (uu___205_23049.unmeta);
                          unascribe = (uu___205_23049.unascribe);
                          in_full_norm_request =
                            (uu___205_23049.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___205_23049.weakly_reduce_scrutinee)
                        }  in
                      let uu___206_23054 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___206_23054.tcenv);
                        debug = (uu___206_23054.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___206_23054.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___206_23054.memoize_lazy);
                        normalize_pure_lets =
                          (uu___206_23054.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23094 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23115 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23175  ->
                                    fun uu____23176  ->
                                      match (uu____23175, uu____23176) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23267 = norm_pat env3 p1
                                             in
                                          (match uu____23267 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23115 with
                           | (pats1,env3) ->
                               ((let uu___207_23349 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___207_23349.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___208_23368 = x  in
                            let uu____23369 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___208_23368.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___208_23368.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23369
                            }  in
                          ((let uu___209_23383 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___209_23383.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___210_23394 = x  in
                            let uu____23395 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___210_23394.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___210_23394.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23395
                            }  in
                          ((let uu___211_23409 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___211_23409.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___212_23425 = x  in
                            let uu____23426 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___212_23425.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___212_23425.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23426
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___213_23433 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___213_23433.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23443 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23457 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23457 with
                                  | (p,wopt,e) ->
                                      let uu____23477 = norm_pat env1 p  in
                                      (match uu____23477 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23502 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23502
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23509 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23509
                      then
                        norm
                          (let uu___214_23512 = cfg1  in
                           {
                             steps =
                               (let uu___215_23515 = cfg1.steps  in
                                {
                                  beta = (uu___215_23515.beta);
                                  iota = (uu___215_23515.iota);
                                  zeta = (uu___215_23515.zeta);
                                  weak = (uu___215_23515.weak);
                                  hnf = (uu___215_23515.hnf);
                                  primops = (uu___215_23515.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___215_23515.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___215_23515.unfold_until);
                                  unfold_only = (uu___215_23515.unfold_only);
                                  unfold_fully =
                                    (uu___215_23515.unfold_fully);
                                  unfold_attr = (uu___215_23515.unfold_attr);
                                  unfold_tac = (uu___215_23515.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___215_23515.pure_subterms_within_computations);
                                  simplify = (uu___215_23515.simplify);
                                  erase_universes =
                                    (uu___215_23515.erase_universes);
                                  allow_unbound_universes =
                                    (uu___215_23515.allow_unbound_universes);
                                  reify_ = (uu___215_23515.reify_);
                                  compress_uvars =
                                    (uu___215_23515.compress_uvars);
                                  no_full_norm =
                                    (uu___215_23515.no_full_norm);
                                  check_no_uvars =
                                    (uu___215_23515.check_no_uvars);
                                  unmeta = (uu___215_23515.unmeta);
                                  unascribe = (uu___215_23515.unascribe);
                                  in_full_norm_request =
                                    (uu___215_23515.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___214_23512.tcenv);
                             debug = (uu___214_23512.debug);
                             delta_level = (uu___214_23512.delta_level);
                             primitive_steps =
                               (uu___214_23512.primitive_steps);
                             strong = (uu___214_23512.strong);
                             memoize_lazy = (uu___214_23512.memoize_lazy);
                             normalize_pure_lets =
                               (uu___214_23512.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23517 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23517)
                    in
                 let rec is_cons head1 =
                   let uu____23524 =
                     let uu____23525 = FStar_Syntax_Subst.compress head1  in
                     uu____23525.FStar_Syntax_Syntax.n  in
                   match uu____23524 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23529) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23534 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23535;
                         FStar_Syntax_Syntax.fv_delta = uu____23536;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23537;
                         FStar_Syntax_Syntax.fv_delta = uu____23538;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23539);_}
                       -> true
                   | uu____23546 -> false  in
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
                   let uu____23707 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23707 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23794 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23833 ->
                                 let uu____23834 =
                                   let uu____23835 = is_cons head1  in
                                   Prims.op_Negation uu____23835  in
                                 FStar_Util.Inr uu____23834)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23860 =
                              let uu____23861 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23861.FStar_Syntax_Syntax.n  in
                            (match uu____23860 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23879 ->
                                 let uu____23880 =
                                   let uu____23881 = is_cons head1  in
                                   Prims.op_Negation uu____23881  in
                                 FStar_Util.Inr uu____23880))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____23950)::rest_a,(p1,uu____23953)::rest_p) ->
                       let uu____23997 = matches_pat t2 p1  in
                       (match uu____23997 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24046 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24156 = matches_pat scrutinee1 p1  in
                       (match uu____24156 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24196  ->
                                  let uu____24197 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24198 =
                                    let uu____24199 =
                                      FStar_List.map
                                        (fun uu____24209  ->
                                           match uu____24209 with
                                           | (uu____24214,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24199
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24197 uu____24198);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24246  ->
                                       match uu____24246 with
                                       | (bv,t2) ->
                                           let uu____24269 =
                                             let uu____24276 =
                                               let uu____24279 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24279
                                                in
                                             let uu____24280 =
                                               let uu____24281 =
                                                 let uu____24312 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24312, false)
                                                  in
                                               Clos uu____24281  in
                                             (uu____24276, uu____24280)  in
                                           uu____24269 :: env2) env1 s
                                 in
                              let uu____24429 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24429)))
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
    let uu____24456 =
      let uu____24459 = FStar_ST.op_Bang plugins  in p :: uu____24459  in
    FStar_ST.op_Colon_Equals plugins uu____24456  in
  let retrieve uu____24567 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24644  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___114_24685  ->
                  match uu___114_24685 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24689 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24695 -> d  in
        let uu____24698 = to_fsteps s  in
        let uu____24699 =
          let uu____24700 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24701 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24702 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24703 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____24704 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24705 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24700;
            primop = uu____24701;
            b380 = uu____24702;
            wpe = uu____24703;
            norm_delayed = uu____24704;
            print_normalized = uu____24705
          }  in
        let uu____24706 =
          let uu____24709 =
            let uu____24712 = retrieve_plugins ()  in
            FStar_List.append uu____24712 psteps  in
          add_steps built_in_primitive_steps uu____24709  in
        let uu____24715 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24717 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24717)
           in
        {
          steps = uu____24698;
          tcenv = e;
          debug = uu____24699;
          delta_level = d1;
          primitive_steps = uu____24706;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24715
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
      fun t  -> let uu____24799 = config s e  in norm_comp uu____24799 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24816 = config [] env  in norm_universe uu____24816 [] u
  
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
        let uu____24840 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24840  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24847 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___216_24866 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___216_24866.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___216_24866.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24873 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24873
          then
            let ct1 =
              let uu____24875 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24875 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24882 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24882
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___217_24886 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___217_24886.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___217_24886.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___217_24886.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___218_24888 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___218_24888.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___218_24888.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___218_24888.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___218_24888.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___219_24889 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___219_24889.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___219_24889.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24891 -> c
  
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
        let uu____24909 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24909  in
      let uu____24916 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24916
      then
        let uu____24917 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24917 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24923  ->
                 let uu____24924 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24924)
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
            ((let uu____24945 =
                let uu____24950 =
                  let uu____24951 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24951
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24950)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24945);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24966 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24966 [] c
        with
        | e ->
            ((let uu____24979 =
                let uu____24984 =
                  let uu____24985 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24985
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24984)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24979);
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
                   let uu____25030 =
                     let uu____25031 =
                       let uu____25038 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25038)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25031  in
                   mk uu____25030 t01.FStar_Syntax_Syntax.pos
               | uu____25043 -> t2)
          | uu____25044 -> t2  in
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
        let uu____25108 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25108 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25137 ->
                 let uu____25144 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25144 with
                  | (actuals,uu____25154,uu____25155) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25169 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25169 with
                         | (binders,args) ->
                             let uu____25186 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25186
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
      | uu____25198 ->
          let uu____25199 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25199 with
           | (head1,args) ->
               let uu____25236 =
                 let uu____25237 = FStar_Syntax_Subst.compress head1  in
                 uu____25237.FStar_Syntax_Syntax.n  in
               (match uu____25236 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25240,thead) ->
                    let uu____25266 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25266 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25308 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___224_25316 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___224_25316.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___224_25316.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___224_25316.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___224_25316.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___224_25316.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___224_25316.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___224_25316.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___224_25316.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___224_25316.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___224_25316.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___224_25316.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___224_25316.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___224_25316.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___224_25316.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___224_25316.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___224_25316.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___224_25316.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___224_25316.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___224_25316.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___224_25316.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___224_25316.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___224_25316.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___224_25316.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___224_25316.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___224_25316.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___224_25316.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___224_25316.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___224_25316.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___224_25316.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___224_25316.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___224_25316.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___224_25316.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___224_25316.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___224_25316.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25308 with
                            | (uu____25317,ty,uu____25319) ->
                                eta_expand_with_type env t ty))
                | uu____25320 ->
                    let uu____25321 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___225_25329 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___225_25329.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___225_25329.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___225_25329.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___225_25329.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___225_25329.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___225_25329.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___225_25329.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___225_25329.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___225_25329.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___225_25329.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___225_25329.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___225_25329.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___225_25329.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___225_25329.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___225_25329.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___225_25329.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___225_25329.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___225_25329.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___225_25329.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___225_25329.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___225_25329.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___225_25329.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___225_25329.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___225_25329.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___225_25329.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___225_25329.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___225_25329.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___225_25329.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___225_25329.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___225_25329.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___225_25329.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___225_25329.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___225_25329.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___225_25329.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25321 with
                     | (uu____25330,ty,uu____25332) ->
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
      let uu___226_25405 = x  in
      let uu____25406 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___226_25405.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___226_25405.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25406
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25409 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25434 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25435 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25436 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25437 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25444 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25445 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25446 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___227_25476 = rc  in
          let uu____25477 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25484 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___227_25476.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25477;
            FStar_Syntax_Syntax.residual_flags = uu____25484
          }  in
        let uu____25487 =
          let uu____25488 =
            let uu____25505 = elim_delayed_subst_binders bs  in
            let uu____25512 = elim_delayed_subst_term t2  in
            let uu____25513 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25505, uu____25512, uu____25513)  in
          FStar_Syntax_Syntax.Tm_abs uu____25488  in
        mk1 uu____25487
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25542 =
          let uu____25543 =
            let uu____25556 = elim_delayed_subst_binders bs  in
            let uu____25563 = elim_delayed_subst_comp c  in
            (uu____25556, uu____25563)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25543  in
        mk1 uu____25542
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25576 =
          let uu____25577 =
            let uu____25584 = elim_bv bv  in
            let uu____25585 = elim_delayed_subst_term phi  in
            (uu____25584, uu____25585)  in
          FStar_Syntax_Syntax.Tm_refine uu____25577  in
        mk1 uu____25576
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25608 =
          let uu____25609 =
            let uu____25624 = elim_delayed_subst_term t2  in
            let uu____25625 = elim_delayed_subst_args args  in
            (uu____25624, uu____25625)  in
          FStar_Syntax_Syntax.Tm_app uu____25609  in
        mk1 uu____25608
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___228_25691 = p  in
              let uu____25692 =
                let uu____25693 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25693  in
              {
                FStar_Syntax_Syntax.v = uu____25692;
                FStar_Syntax_Syntax.p =
                  (uu___228_25691.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___229_25695 = p  in
              let uu____25696 =
                let uu____25697 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25697  in
              {
                FStar_Syntax_Syntax.v = uu____25696;
                FStar_Syntax_Syntax.p =
                  (uu___229_25695.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___230_25704 = p  in
              let uu____25705 =
                let uu____25706 =
                  let uu____25713 = elim_bv x  in
                  let uu____25714 = elim_delayed_subst_term t0  in
                  (uu____25713, uu____25714)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25706  in
              {
                FStar_Syntax_Syntax.v = uu____25705;
                FStar_Syntax_Syntax.p =
                  (uu___230_25704.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___231_25733 = p  in
              let uu____25734 =
                let uu____25735 =
                  let uu____25748 =
                    FStar_List.map
                      (fun uu____25771  ->
                         match uu____25771 with
                         | (x,b) ->
                             let uu____25784 = elim_pat x  in
                             (uu____25784, b)) pats
                     in
                  (fv, uu____25748)  in
                FStar_Syntax_Syntax.Pat_cons uu____25735  in
              {
                FStar_Syntax_Syntax.v = uu____25734;
                FStar_Syntax_Syntax.p =
                  (uu___231_25733.FStar_Syntax_Syntax.p)
              }
          | uu____25797 -> p  in
        let elim_branch uu____25821 =
          match uu____25821 with
          | (pat,wopt,t3) ->
              let uu____25847 = elim_pat pat  in
              let uu____25850 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25853 = elim_delayed_subst_term t3  in
              (uu____25847, uu____25850, uu____25853)
           in
        let uu____25858 =
          let uu____25859 =
            let uu____25882 = elim_delayed_subst_term t2  in
            let uu____25883 = FStar_List.map elim_branch branches  in
            (uu____25882, uu____25883)  in
          FStar_Syntax_Syntax.Tm_match uu____25859  in
        mk1 uu____25858
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25994 =
          match uu____25994 with
          | (tc,topt) ->
              let uu____26029 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26039 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26039
                | FStar_Util.Inr c ->
                    let uu____26041 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26041
                 in
              let uu____26042 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26029, uu____26042)
           in
        let uu____26051 =
          let uu____26052 =
            let uu____26079 = elim_delayed_subst_term t2  in
            let uu____26080 = elim_ascription a  in
            (uu____26079, uu____26080, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26052  in
        mk1 uu____26051
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___232_26127 = lb  in
          let uu____26128 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26131 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___232_26127.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___232_26127.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26128;
            FStar_Syntax_Syntax.lbeff =
              (uu___232_26127.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26131;
            FStar_Syntax_Syntax.lbattrs =
              (uu___232_26127.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___232_26127.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26134 =
          let uu____26135 =
            let uu____26148 =
              let uu____26155 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26155)  in
            let uu____26164 = elim_delayed_subst_term t2  in
            (uu____26148, uu____26164)  in
          FStar_Syntax_Syntax.Tm_let uu____26135  in
        mk1 uu____26134
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26197 =
          let uu____26198 =
            let uu____26215 = elim_delayed_subst_term t2  in
            (uv, uu____26215)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26198  in
        mk1 uu____26197
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26233 =
          let uu____26234 =
            let uu____26241 = elim_delayed_subst_term tm  in
            (uu____26241, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26234  in
        mk1 uu____26233
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26248 =
          let uu____26249 =
            let uu____26256 = elim_delayed_subst_term t2  in
            let uu____26257 = elim_delayed_subst_meta md  in
            (uu____26256, uu____26257)  in
          FStar_Syntax_Syntax.Tm_meta uu____26249  in
        mk1 uu____26248

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___115_26264  ->
         match uu___115_26264 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26268 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26268
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
        let uu____26291 =
          let uu____26292 =
            let uu____26301 = elim_delayed_subst_term t  in
            (uu____26301, uopt)  in
          FStar_Syntax_Syntax.Total uu____26292  in
        mk1 uu____26291
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26314 =
          let uu____26315 =
            let uu____26324 = elim_delayed_subst_term t  in
            (uu____26324, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26315  in
        mk1 uu____26314
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___233_26329 = ct  in
          let uu____26330 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26333 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26342 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___233_26329.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___233_26329.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26330;
            FStar_Syntax_Syntax.effect_args = uu____26333;
            FStar_Syntax_Syntax.flags = uu____26342
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___116_26345  ->
    match uu___116_26345 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26357 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26357
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26390 =
          let uu____26397 = elim_delayed_subst_term t  in (m, uu____26397)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26390
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26405 =
          let uu____26414 = elim_delayed_subst_term t  in
          (m1, m2, uu____26414)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26405
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26437  ->
         match uu____26437 with
         | (t,q) ->
             let uu____26448 = elim_delayed_subst_term t  in (uu____26448, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26468  ->
         match uu____26468 with
         | (x,q) ->
             let uu____26479 =
               let uu___234_26480 = x  in
               let uu____26481 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___234_26480.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___234_26480.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26481
               }  in
             (uu____26479, q)) bs

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
            | (uu____26565,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26571,FStar_Util.Inl t) ->
                let uu____26577 =
                  let uu____26584 =
                    let uu____26585 =
                      let uu____26598 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26598)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26585  in
                  FStar_Syntax_Syntax.mk uu____26584  in
                uu____26577 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26602 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26602 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26630 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26685 ->
                    let uu____26686 =
                      let uu____26695 =
                        let uu____26696 = FStar_Syntax_Subst.compress t4  in
                        uu____26696.FStar_Syntax_Syntax.n  in
                      (uu____26695, tc)  in
                    (match uu____26686 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26721) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26758) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26797,FStar_Util.Inl uu____26798) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26821 -> failwith "Impossible")
                 in
              (match uu____26630 with
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
          let uu____26934 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26934 with
          | (univ_names1,binders1,tc) ->
              let uu____26992 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26992)
  
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
          let uu____27035 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____27035 with
          | (univ_names1,binders1,tc) ->
              let uu____27095 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27095)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27132 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27132 with
           | (univ_names1,binders1,typ1) ->
               let uu___235_27160 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_27160.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_27160.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_27160.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_27160.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___236_27181 = s  in
          let uu____27182 =
            let uu____27183 =
              let uu____27192 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27192, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27183  in
          {
            FStar_Syntax_Syntax.sigel = uu____27182;
            FStar_Syntax_Syntax.sigrng =
              (uu___236_27181.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___236_27181.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___236_27181.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___236_27181.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27209 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27209 with
           | (univ_names1,uu____27227,typ1) ->
               let uu___237_27241 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___237_27241.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___237_27241.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___237_27241.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___237_27241.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27247 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27247 with
           | (univ_names1,uu____27265,typ1) ->
               let uu___238_27279 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_27279.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_27279.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_27279.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_27279.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27313 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27313 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27338 =
                            let uu____27339 =
                              let uu____27340 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27340  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27339
                             in
                          elim_delayed_subst_term uu____27338  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___239_27343 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___239_27343.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___239_27343.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___239_27343.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___239_27343.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___240_27344 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___240_27344.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___240_27344.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___240_27344.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___240_27344.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___241_27356 = s  in
          let uu____27357 =
            let uu____27358 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27358  in
          {
            FStar_Syntax_Syntax.sigel = uu____27357;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_27356.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_27356.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_27356.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_27356.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27362 = elim_uvars_aux_t env us [] t  in
          (match uu____27362 with
           | (us1,uu____27380,t1) ->
               let uu___242_27394 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_27394.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_27394.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_27394.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_27394.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27395 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27397 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27397 with
           | (univs1,binders,signature) ->
               let uu____27425 =
                 let uu____27434 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27434 with
                 | (univs_opening,univs2) ->
                     let uu____27461 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27461)
                  in
               (match uu____27425 with
                | (univs_opening,univs_closing) ->
                    let uu____27478 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27484 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27485 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27484, uu____27485)  in
                    (match uu____27478 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27509 =
                           match uu____27509 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27527 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27527 with
                                | (us1,t1) ->
                                    let uu____27538 =
                                      let uu____27543 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27550 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27543, uu____27550)  in
                                    (match uu____27538 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27563 =
                                           let uu____27568 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27577 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27568, uu____27577)  in
                                         (match uu____27563 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27593 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27593
                                                 in
                                              let uu____27594 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27594 with
                                               | (uu____27615,uu____27616,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27631 =
                                                       let uu____27632 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27632
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27631
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27639 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27639 with
                           | (uu____27652,uu____27653,t1) -> t1  in
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
                             | uu____27715 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27734 =
                               let uu____27735 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27735.FStar_Syntax_Syntax.n  in
                             match uu____27734 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27794 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27825 =
                               let uu____27826 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27826.FStar_Syntax_Syntax.n  in
                             match uu____27825 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27847) ->
                                 let uu____27868 = destruct_action_body body
                                    in
                                 (match uu____27868 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27913 ->
                                 let uu____27914 = destruct_action_body t  in
                                 (match uu____27914 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27963 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27963 with
                           | (action_univs,t) ->
                               let uu____27972 = destruct_action_typ_templ t
                                  in
                               (match uu____27972 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___243_28013 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___243_28013.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___243_28013.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___244_28015 = ed  in
                           let uu____28016 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____28017 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____28018 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____28019 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____28020 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____28021 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____28022 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____28023 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____28024 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____28025 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____28026 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____28027 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____28028 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____28029 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___244_28015.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___244_28015.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____28016;
                             FStar_Syntax_Syntax.bind_wp = uu____28017;
                             FStar_Syntax_Syntax.if_then_else = uu____28018;
                             FStar_Syntax_Syntax.ite_wp = uu____28019;
                             FStar_Syntax_Syntax.stronger = uu____28020;
                             FStar_Syntax_Syntax.close_wp = uu____28021;
                             FStar_Syntax_Syntax.assert_p = uu____28022;
                             FStar_Syntax_Syntax.assume_p = uu____28023;
                             FStar_Syntax_Syntax.null_wp = uu____28024;
                             FStar_Syntax_Syntax.trivial = uu____28025;
                             FStar_Syntax_Syntax.repr = uu____28026;
                             FStar_Syntax_Syntax.return_repr = uu____28027;
                             FStar_Syntax_Syntax.bind_repr = uu____28028;
                             FStar_Syntax_Syntax.actions = uu____28029;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___244_28015.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___245_28032 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___245_28032.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___245_28032.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___245_28032.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___245_28032.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___117_28051 =
            match uu___117_28051 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28078 = elim_uvars_aux_t env us [] t  in
                (match uu____28078 with
                 | (us1,uu____28102,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___246_28121 = sub_eff  in
            let uu____28122 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28125 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___246_28121.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___246_28121.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28122;
              FStar_Syntax_Syntax.lift = uu____28125
            }  in
          let uu___247_28128 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___247_28128.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___247_28128.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___247_28128.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___247_28128.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28138 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28138 with
           | (univ_names1,binders1,comp1) ->
               let uu___248_28172 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_28172.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_28172.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_28172.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_28172.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28183 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28184 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  