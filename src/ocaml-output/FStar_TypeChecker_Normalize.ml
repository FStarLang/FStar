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
                | (Arg (c,uu____12674,uu____12675))::stack_rest ->
                    (match c with
                     | Univ uu____12679 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12688 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12709  ->
                                    let uu____12710 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12710);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12750  ->
                                    let uu____12751 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12751);
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
                       (fun uu____12829  ->
                          let uu____12830 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12830);
                     norm cfg env stack1 t1)
                | (Match uu____12831)::uu____12832 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_12846 = cfg.steps  in
                             {
                               beta = (uu___175_12846.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_12846.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_12846.unfold_until);
                               unfold_only = (uu___175_12846.unfold_only);
                               unfold_fully = (uu___175_12846.unfold_fully);
                               unfold_attr = (uu___175_12846.unfold_attr);
                               unfold_tac = (uu___175_12846.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_12846.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_12846.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_12846.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_12846.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_12846.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_12846.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_12848 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_12848.tcenv);
                               debug = (uu___176_12848.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_12848.primitive_steps);
                               strong = (uu___176_12848.strong);
                               memoize_lazy = (uu___176_12848.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_12848.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12850 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12850 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12892  -> dummy :: env1) env)
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
                                          let uu____12929 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12929)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_12934 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_12934.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_12934.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12935 -> lopt  in
                           (log cfg
                              (fun uu____12941  ->
                                 let uu____12942 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12942);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_12951 = cfg  in
                               {
                                 steps = (uu___178_12951.steps);
                                 tcenv = (uu___178_12951.tcenv);
                                 debug = (uu___178_12951.debug);
                                 delta_level = (uu___178_12951.delta_level);
                                 primitive_steps =
                                   (uu___178_12951.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_12951.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_12951.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____12962)::uu____12963 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_12973 = cfg.steps  in
                             {
                               beta = (uu___175_12973.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_12973.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_12973.unfold_until);
                               unfold_only = (uu___175_12973.unfold_only);
                               unfold_fully = (uu___175_12973.unfold_fully);
                               unfold_attr = (uu___175_12973.unfold_attr);
                               unfold_tac = (uu___175_12973.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_12973.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_12973.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_12973.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_12973.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_12973.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_12973.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_12975 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_12975.tcenv);
                               debug = (uu___176_12975.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_12975.primitive_steps);
                               strong = (uu___176_12975.strong);
                               memoize_lazy = (uu___176_12975.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_12975.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12977 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12977 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13019  -> dummy :: env1) env)
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
                                          let uu____13056 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13056)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13061 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13061.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13061.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13062 -> lopt  in
                           (log cfg
                              (fun uu____13068  ->
                                 let uu____13069 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13069);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13078 = cfg  in
                               {
                                 steps = (uu___178_13078.steps);
                                 tcenv = (uu___178_13078.tcenv);
                                 debug = (uu___178_13078.debug);
                                 delta_level = (uu___178_13078.delta_level);
                                 primitive_steps =
                                   (uu___178_13078.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13078.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13078.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13089)::uu____13090 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13102 = cfg.steps  in
                             {
                               beta = (uu___175_13102.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13102.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13102.unfold_until);
                               unfold_only = (uu___175_13102.unfold_only);
                               unfold_fully = (uu___175_13102.unfold_fully);
                               unfold_attr = (uu___175_13102.unfold_attr);
                               unfold_tac = (uu___175_13102.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13102.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13102.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13102.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13102.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13102.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13102.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13104 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13104.tcenv);
                               debug = (uu___176_13104.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13104.primitive_steps);
                               strong = (uu___176_13104.strong);
                               memoize_lazy = (uu___176_13104.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13104.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13106 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13106 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13148  -> dummy :: env1) env)
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
                                          let uu____13185 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13185)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13190 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13190.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13190.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13191 -> lopt  in
                           (log cfg
                              (fun uu____13197  ->
                                 let uu____13198 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13198);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13207 = cfg  in
                               {
                                 steps = (uu___178_13207.steps);
                                 tcenv = (uu___178_13207.tcenv);
                                 debug = (uu___178_13207.debug);
                                 delta_level = (uu___178_13207.delta_level);
                                 primitive_steps =
                                   (uu___178_13207.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13207.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13207.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13218)::uu____13219 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13233 = cfg.steps  in
                             {
                               beta = (uu___175_13233.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13233.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13233.unfold_until);
                               unfold_only = (uu___175_13233.unfold_only);
                               unfold_fully = (uu___175_13233.unfold_fully);
                               unfold_attr = (uu___175_13233.unfold_attr);
                               unfold_tac = (uu___175_13233.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13233.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13233.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13233.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13233.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13233.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13233.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13235 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13235.tcenv);
                               debug = (uu___176_13235.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13235.primitive_steps);
                               strong = (uu___176_13235.strong);
                               memoize_lazy = (uu___176_13235.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13235.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13237 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13237 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13279  -> dummy :: env1) env)
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
                                          let uu____13316 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13316)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13321 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13321.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13321.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13322 -> lopt  in
                           (log cfg
                              (fun uu____13328  ->
                                 let uu____13329 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13329);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13338 = cfg  in
                               {
                                 steps = (uu___178_13338.steps);
                                 tcenv = (uu___178_13338.tcenv);
                                 debug = (uu___178_13338.debug);
                                 delta_level = (uu___178_13338.delta_level);
                                 primitive_steps =
                                   (uu___178_13338.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13338.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13338.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13349)::uu____13350 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13364 = cfg.steps  in
                             {
                               beta = (uu___175_13364.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13364.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13364.unfold_until);
                               unfold_only = (uu___175_13364.unfold_only);
                               unfold_fully = (uu___175_13364.unfold_fully);
                               unfold_attr = (uu___175_13364.unfold_attr);
                               unfold_tac = (uu___175_13364.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13364.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13364.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13364.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13364.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13364.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13364.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13366 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13366.tcenv);
                               debug = (uu___176_13366.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13366.primitive_steps);
                               strong = (uu___176_13366.strong);
                               memoize_lazy = (uu___176_13366.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13366.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13368 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13368 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13410  -> dummy :: env1) env)
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
                                          let uu____13447 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13447)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13452 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13452.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13452.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13453 -> lopt  in
                           (log cfg
                              (fun uu____13459  ->
                                 let uu____13460 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13460);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13469 = cfg  in
                               {
                                 steps = (uu___178_13469.steps);
                                 tcenv = (uu___178_13469.tcenv);
                                 debug = (uu___178_13469.debug);
                                 delta_level = (uu___178_13469.delta_level);
                                 primitive_steps =
                                   (uu___178_13469.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13469.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13469.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13480)::uu____13481 ->
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
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___175_13618 = cfg.steps  in
                             {
                               beta = (uu___175_13618.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___175_13618.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___175_13618.unfold_until);
                               unfold_only = (uu___175_13618.unfold_only);
                               unfold_fully = (uu___175_13618.unfold_fully);
                               unfold_attr = (uu___175_13618.unfold_attr);
                               unfold_tac = (uu___175_13618.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___175_13618.erase_universes);
                               allow_unbound_universes =
                                 (uu___175_13618.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___175_13618.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___175_13618.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___175_13618.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___175_13618.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___176_13620 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___176_13620.tcenv);
                               debug = (uu___176_13620.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___176_13620.primitive_steps);
                               strong = (uu___176_13620.strong);
                               memoize_lazy = (uu___176_13620.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___176_13620.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13622 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13622 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13664  -> dummy :: env1) env)
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
                                          let uu____13701 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13701)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___177_13706 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___177_13706.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___177_13706.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13707 -> lopt  in
                           (log cfg
                              (fun uu____13713  ->
                                 let uu____13714 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13714);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___178_13723 = cfg  in
                               {
                                 steps = (uu___178_13723.steps);
                                 tcenv = (uu___178_13723.tcenv);
                                 debug = (uu___178_13723.debug);
                                 delta_level = (uu___178_13723.delta_level);
                                 primitive_steps =
                                   (uu___178_13723.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___178_13723.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___178_13723.normalize_pure_lets)
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
                      (fun uu____13772  ->
                         fun stack1  ->
                           match uu____13772 with
                           | (a,aq) ->
                               let uu____13784 =
                                 let uu____13785 =
                                   let uu____13792 =
                                     let uu____13793 =
                                       let uu____13824 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13824, false)  in
                                     Clos uu____13793  in
                                   (uu____13792, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13785  in
                               uu____13784 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13908  ->
                     let uu____13909 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13909);
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
                             ((let uu___179_13945 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___179_13945.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___179_13945.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13946 ->
                      let uu____13951 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13951)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13954 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13954 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13985 =
                          let uu____13986 =
                            let uu____13993 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___180_13995 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___180_13995.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___180_13995.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13993)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13986  in
                        mk uu____13985 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14014 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14014
               else
                 (let uu____14016 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14016 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14024 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14048  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14024 c1  in
                      let t2 =
                        let uu____14070 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14070 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14181)::uu____14182 ->
                    (log cfg
                       (fun uu____14195  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14196)::uu____14197 ->
                    (log cfg
                       (fun uu____14208  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14209,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14210;
                                   FStar_Syntax_Syntax.vars = uu____14211;_},uu____14212,uu____14213))::uu____14214
                    ->
                    (log cfg
                       (fun uu____14223  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14224)::uu____14225 ->
                    (log cfg
                       (fun uu____14236  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14237 ->
                    (log cfg
                       (fun uu____14240  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14244  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14261 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14261
                         | FStar_Util.Inr c ->
                             let uu____14269 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14269
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14282 =
                               let uu____14283 =
                                 let uu____14310 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14310, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14283
                                in
                             mk uu____14282 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14329 ->
                           let uu____14330 =
                             let uu____14331 =
                               let uu____14332 =
                                 let uu____14359 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14359, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14332
                                in
                             mk uu____14331 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14330))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___181_14436 = cfg  in
                   {
                     steps =
                       (let uu___182_14439 = cfg.steps  in
                        {
                          beta = (uu___182_14439.beta);
                          iota = (uu___182_14439.iota);
                          zeta = (uu___182_14439.zeta);
                          weak = true;
                          hnf = (uu___182_14439.hnf);
                          primops = (uu___182_14439.primops);
                          do_not_unfold_pure_lets =
                            (uu___182_14439.do_not_unfold_pure_lets);
                          unfold_until = (uu___182_14439.unfold_until);
                          unfold_only = (uu___182_14439.unfold_only);
                          unfold_fully = (uu___182_14439.unfold_fully);
                          unfold_attr = (uu___182_14439.unfold_attr);
                          unfold_tac = (uu___182_14439.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___182_14439.pure_subterms_within_computations);
                          simplify = (uu___182_14439.simplify);
                          erase_universes = (uu___182_14439.erase_universes);
                          allow_unbound_universes =
                            (uu___182_14439.allow_unbound_universes);
                          reify_ = (uu___182_14439.reify_);
                          compress_uvars = (uu___182_14439.compress_uvars);
                          no_full_norm = (uu___182_14439.no_full_norm);
                          check_no_uvars = (uu___182_14439.check_no_uvars);
                          unmeta = (uu___182_14439.unmeta);
                          unascribe = (uu___182_14439.unascribe);
                          in_full_norm_request =
                            (uu___182_14439.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___182_14439.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___181_14436.tcenv);
                     debug = (uu___181_14436.debug);
                     delta_level = (uu___181_14436.delta_level);
                     primitive_steps = (uu___181_14436.primitive_steps);
                     strong = (uu___181_14436.strong);
                     memoize_lazy = (uu___181_14436.memoize_lazy);
                     normalize_pure_lets =
                       (uu___181_14436.normalize_pure_lets)
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
                         let uu____14475 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14475 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___183_14495 = cfg  in
                               let uu____14496 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___183_14495.steps);
                                 tcenv = uu____14496;
                                 debug = (uu___183_14495.debug);
                                 delta_level = (uu___183_14495.delta_level);
                                 primitive_steps =
                                   (uu___183_14495.primitive_steps);
                                 strong = (uu___183_14495.strong);
                                 memoize_lazy = (uu___183_14495.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___183_14495.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14503 =
                                 let uu____14504 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14504  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14503
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___184_14507 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___184_14507.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___184_14507.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___184_14507.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___184_14507.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14508 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14508
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14519,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14520;
                               FStar_Syntax_Syntax.lbunivs = uu____14521;
                               FStar_Syntax_Syntax.lbtyp = uu____14522;
                               FStar_Syntax_Syntax.lbeff = uu____14523;
                               FStar_Syntax_Syntax.lbdef = uu____14524;
                               FStar_Syntax_Syntax.lbattrs = uu____14525;
                               FStar_Syntax_Syntax.lbpos = uu____14526;_}::uu____14527),uu____14528)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14568 =
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
               if uu____14568
               then
                 let binder =
                   let uu____14570 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14570  in
                 let env1 =
                   let uu____14580 =
                     let uu____14587 =
                       let uu____14588 =
                         let uu____14619 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14619,
                           false)
                          in
                       Clos uu____14588  in
                     ((FStar_Pervasives_Native.Some binder), uu____14587)  in
                   uu____14580 :: env  in
                 (log cfg
                    (fun uu____14712  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14716  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14717 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14717))
                 else
                   (let uu____14719 =
                      let uu____14724 =
                        let uu____14725 =
                          let uu____14726 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14726
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14725]  in
                      FStar_Syntax_Subst.open_term uu____14724 body  in
                    match uu____14719 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14735  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14743 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14743  in
                            FStar_Util.Inl
                              (let uu___185_14753 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___185_14753.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___185_14753.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14756  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___186_14758 = lb  in
                             let uu____14759 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___186_14758.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___186_14758.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14759;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___186_14758.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___186_14758.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14794  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___187_14817 = cfg  in
                             {
                               steps = (uu___187_14817.steps);
                               tcenv = (uu___187_14817.tcenv);
                               debug = (uu___187_14817.debug);
                               delta_level = (uu___187_14817.delta_level);
                               primitive_steps =
                                 (uu___187_14817.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___187_14817.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___187_14817.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14820  ->
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
               let uu____14837 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14837 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14873 =
                               let uu___188_14874 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___188_14874.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___188_14874.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14873  in
                           let uu____14875 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14875 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14901 =
                                   FStar_List.map (fun uu____14917  -> dummy)
                                     lbs1
                                    in
                                 let uu____14918 =
                                   let uu____14927 =
                                     FStar_List.map
                                       (fun uu____14947  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14927 env  in
                                 FStar_List.append uu____14901 uu____14918
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14971 =
                                       let uu___189_14972 = rc  in
                                       let uu____14973 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___189_14972.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14973;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___189_14972.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14971
                                 | uu____14980 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___190_14984 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___190_14984.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___190_14984.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___190_14984.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___190_14984.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14994 =
                        FStar_List.map (fun uu____15010  -> dummy) lbs2  in
                      FStar_List.append uu____14994 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15018 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15018 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___191_15034 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___191_15034.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___191_15034.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15061 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15061
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15080 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15156  ->
                        match uu____15156 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___192_15277 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___192_15277.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___192_15277.FStar_Syntax_Syntax.sort)
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
               (match uu____15080 with
                | (rec_env,memos,uu____15490) ->
                    let uu____15543 =
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
                             let uu____15866 =
                               let uu____15873 =
                                 let uu____15874 =
                                   let uu____15905 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15905, false)
                                    in
                                 Clos uu____15874  in
                               (FStar_Pervasives_Native.None, uu____15873)
                                in
                             uu____15866 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16015  ->
                     let uu____16016 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16016);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16038 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16040::uu____16041 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16046) ->
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
                             | uu____16069 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16083 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16083
                              | uu____16094 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16098 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16124 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16142 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16159 =
                        let uu____16160 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16161 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16160 uu____16161
                         in
                      failwith uu____16159
                    else rebuild cfg env stack t2
                | uu____16163 -> norm cfg env stack t2))

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
                let uu____16173 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16173  in
              let uu____16174 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16174 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16187  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16198  ->
                        let uu____16199 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16200 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16199 uu____16200);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16205 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16205 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16214))::stack1 ->
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
                      | uu____16269 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16272 ->
                          let uu____16275 =
                            let uu____16276 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16276
                             in
                          failwith uu____16275
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
                  let uu___193_16300 = cfg  in
                  let uu____16301 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16301;
                    tcenv = (uu___193_16300.tcenv);
                    debug = (uu___193_16300.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___193_16300.primitive_steps);
                    strong = (uu___193_16300.strong);
                    memoize_lazy = (uu___193_16300.memoize_lazy);
                    normalize_pure_lets =
                      (uu___193_16300.normalize_pure_lets)
                  }
                else
                  (let uu___194_16303 = cfg  in
                   {
                     steps =
                       (let uu___195_16306 = cfg.steps  in
                        {
                          beta = (uu___195_16306.beta);
                          iota = (uu___195_16306.iota);
                          zeta = false;
                          weak = (uu___195_16306.weak);
                          hnf = (uu___195_16306.hnf);
                          primops = (uu___195_16306.primops);
                          do_not_unfold_pure_lets =
                            (uu___195_16306.do_not_unfold_pure_lets);
                          unfold_until = (uu___195_16306.unfold_until);
                          unfold_only = (uu___195_16306.unfold_only);
                          unfold_fully = (uu___195_16306.unfold_fully);
                          unfold_attr = (uu___195_16306.unfold_attr);
                          unfold_tac = (uu___195_16306.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___195_16306.pure_subterms_within_computations);
                          simplify = (uu___195_16306.simplify);
                          erase_universes = (uu___195_16306.erase_universes);
                          allow_unbound_universes =
                            (uu___195_16306.allow_unbound_universes);
                          reify_ = (uu___195_16306.reify_);
                          compress_uvars = (uu___195_16306.compress_uvars);
                          no_full_norm = (uu___195_16306.no_full_norm);
                          check_no_uvars = (uu___195_16306.check_no_uvars);
                          unmeta = (uu___195_16306.unmeta);
                          unascribe = (uu___195_16306.unascribe);
                          in_full_norm_request =
                            (uu___195_16306.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___195_16306.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___194_16303.tcenv);
                     debug = (uu___194_16303.debug);
                     delta_level = (uu___194_16303.delta_level);
                     primitive_steps = (uu___194_16303.primitive_steps);
                     strong = (uu___194_16303.strong);
                     memoize_lazy = (uu___194_16303.memoize_lazy);
                     normalize_pure_lets =
                       (uu___194_16303.normalize_pure_lets)
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
                  (fun uu____16336  ->
                     let uu____16337 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16338 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16337
                       uu____16338);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16340 =
                   let uu____16341 = FStar_Syntax_Subst.compress head3  in
                   uu____16341.FStar_Syntax_Syntax.n  in
                 match uu____16340 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16359 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16359
                        in
                     let uu____16360 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16360 with
                      | (uu____16361,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16367 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16377 =
                                   let uu____16378 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16378.FStar_Syntax_Syntax.n  in
                                 match uu____16377 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16384,uu____16385))
                                     ->
                                     let uu____16394 =
                                       let uu____16395 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16395.FStar_Syntax_Syntax.n  in
                                     (match uu____16394 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16401,msrc,uu____16403))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16412 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16412
                                      | uu____16413 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16414 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16415 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16415 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___196_16420 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___196_16420.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___196_16420.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___196_16420.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___196_16420.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___196_16420.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16421 = FStar_List.tl stack  in
                                    let uu____16422 =
                                      let uu____16423 =
                                        let uu____16430 =
                                          let uu____16431 =
                                            let uu____16444 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16444)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16431
                                           in
                                        FStar_Syntax_Syntax.mk uu____16430
                                         in
                                      uu____16423
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16421 uu____16422
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16460 =
                                      let uu____16461 = is_return body  in
                                      match uu____16461 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16465;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16466;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16471 -> false  in
                                    if uu____16460
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
                                         let uu____16494 =
                                           let uu____16501 =
                                             let uu____16502 =
                                               let uu____16519 =
                                                 let uu____16522 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16522]  in
                                               (uu____16519, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16502
                                              in
                                           FStar_Syntax_Syntax.mk uu____16501
                                            in
                                         uu____16494
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16540 =
                                           let uu____16541 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16541.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16540 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16547::uu____16548::[])
                                             ->
                                             let uu____16555 =
                                               let uu____16562 =
                                                 let uu____16563 =
                                                   let uu____16570 =
                                                     let uu____16573 =
                                                       let uu____16574 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16574
                                                        in
                                                     let uu____16575 =
                                                       let uu____16578 =
                                                         let uu____16579 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16579
                                                          in
                                                       [uu____16578]  in
                                                     uu____16573 ::
                                                       uu____16575
                                                      in
                                                   (bind1, uu____16570)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16563
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16562
                                                in
                                             uu____16555
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16587 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16593 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16593
                                         then
                                           let uu____16596 =
                                             let uu____16597 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16597
                                              in
                                           let uu____16598 =
                                             let uu____16601 =
                                               let uu____16602 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16602
                                                in
                                             [uu____16601]  in
                                           uu____16596 :: uu____16598
                                         else []  in
                                       let reified =
                                         let uu____16607 =
                                           let uu____16614 =
                                             let uu____16615 =
                                               let uu____16630 =
                                                 let uu____16633 =
                                                   let uu____16636 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16637 =
                                                     let uu____16640 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16640]  in
                                                   uu____16636 :: uu____16637
                                                    in
                                                 let uu____16641 =
                                                   let uu____16644 =
                                                     let uu____16647 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16648 =
                                                       let uu____16651 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16652 =
                                                         let uu____16655 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16656 =
                                                           let uu____16659 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16659]  in
                                                         uu____16655 ::
                                                           uu____16656
                                                          in
                                                       uu____16651 ::
                                                         uu____16652
                                                        in
                                                     uu____16647 ::
                                                       uu____16648
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16644
                                                    in
                                                 FStar_List.append
                                                   uu____16633 uu____16641
                                                  in
                                               (bind_inst, uu____16630)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16615
                                              in
                                           FStar_Syntax_Syntax.mk uu____16614
                                            in
                                         uu____16607
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16671  ->
                                            let uu____16672 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16673 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16672 uu____16673);
                                       (let uu____16674 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16674 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16698 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16698
                        in
                     let uu____16699 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16699 with
                      | (uu____16700,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16739 =
                                  let uu____16740 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16740.FStar_Syntax_Syntax.n  in
                                match uu____16739 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16746) -> t2
                                | uu____16751 -> head4  in
                              let uu____16752 =
                                let uu____16753 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16753.FStar_Syntax_Syntax.n  in
                              match uu____16752 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16759 -> FStar_Pervasives_Native.None
                               in
                            let uu____16760 = maybe_extract_fv head4  in
                            match uu____16760 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16770 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16770
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16775 = maybe_extract_fv head5
                                     in
                                  match uu____16775 with
                                  | FStar_Pervasives_Native.Some uu____16780
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16781 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16786 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16803 =
                              match uu____16803 with
                              | (e,q) ->
                                  let uu____16810 =
                                    let uu____16811 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16811.FStar_Syntax_Syntax.n  in
                                  (match uu____16810 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16826 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16826
                                   | uu____16827 -> false)
                               in
                            let uu____16828 =
                              let uu____16829 =
                                let uu____16836 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16836 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16829
                               in
                            if uu____16828
                            then
                              let uu____16841 =
                                let uu____16842 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16842
                                 in
                              failwith uu____16841
                            else ());
                           (let uu____16844 = maybe_unfold_action head_app
                               in
                            match uu____16844 with
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
                                   (fun uu____16887  ->
                                      let uu____16888 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16889 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16888 uu____16889);
                                 (let uu____16890 = FStar_List.tl stack  in
                                  norm cfg env uu____16890 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16892) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16916 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16916  in
                     (log cfg
                        (fun uu____16920  ->
                           let uu____16921 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16921);
                      (let uu____16922 = FStar_List.tl stack  in
                       norm cfg env uu____16922 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17043  ->
                               match uu____17043 with
                               | (pat,wopt,tm) ->
                                   let uu____17091 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17091)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17123 = FStar_List.tl stack  in
                     norm cfg env uu____17123 tm
                 | uu____17124 -> fallback ())

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
              (fun uu____17138  ->
                 let uu____17139 = FStar_Ident.string_of_lid msrc  in
                 let uu____17140 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17141 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17139
                   uu____17140 uu____17141);
            (let uu____17142 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17142
             then
               let ed =
                 let uu____17144 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17144  in
               let uu____17145 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17145 with
               | (uu____17146,return_repr) ->
                   let return_inst =
                     let uu____17155 =
                       let uu____17156 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17156.FStar_Syntax_Syntax.n  in
                     match uu____17155 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17162::[]) ->
                         let uu____17169 =
                           let uu____17176 =
                             let uu____17177 =
                               let uu____17184 =
                                 let uu____17187 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17187]  in
                               (return_tm, uu____17184)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17177  in
                           FStar_Syntax_Syntax.mk uu____17176  in
                         uu____17169 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17195 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17198 =
                     let uu____17205 =
                       let uu____17206 =
                         let uu____17221 =
                           let uu____17224 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17225 =
                             let uu____17228 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17228]  in
                           uu____17224 :: uu____17225  in
                         (return_inst, uu____17221)  in
                       FStar_Syntax_Syntax.Tm_app uu____17206  in
                     FStar_Syntax_Syntax.mk uu____17205  in
                   uu____17198 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17237 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17237 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17240 =
                      let uu____17241 = FStar_Ident.text_of_lid msrc  in
                      let uu____17242 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17241 uu____17242
                       in
                    failwith uu____17240
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17243;
                      FStar_TypeChecker_Env.mtarget = uu____17244;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17245;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17267 =
                      let uu____17268 = FStar_Ident.text_of_lid msrc  in
                      let uu____17269 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17268 uu____17269
                       in
                    failwith uu____17267
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17270;
                      FStar_TypeChecker_Env.mtarget = uu____17271;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17272;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17307 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17308 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17307 t FStar_Syntax_Syntax.tun uu____17308))

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
                (fun uu____17364  ->
                   match uu____17364 with
                   | (a,imp) ->
                       let uu____17375 = norm cfg env [] a  in
                       (uu____17375, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17383  ->
             let uu____17384 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17385 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17384 uu____17385);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17409 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17409
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___197_17412 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___197_17412.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___197_17412.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17432 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17432
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___198_17435 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___198_17435.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___198_17435.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17470  ->
                      match uu____17470 with
                      | (a,i) ->
                          let uu____17481 = norm cfg env [] a  in
                          (uu____17481, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___112_17499  ->
                       match uu___112_17499 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17503 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17503
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___199_17511 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___200_17514 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___200_17514.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___199_17511.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___199_17511.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17517  ->
        match uu____17517 with
        | (x,imp) ->
            let uu____17520 =
              let uu___201_17521 = x  in
              let uu____17522 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___201_17521.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___201_17521.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17522
              }  in
            (uu____17520, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17528 =
          FStar_List.fold_left
            (fun uu____17546  ->
               fun b  ->
                 match uu____17546 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17528 with | (nbs,uu____17586) -> FStar_List.rev nbs

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
            let uu____17602 =
              let uu___202_17603 = rc  in
              let uu____17604 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___202_17603.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17604;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___202_17603.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17602
        | uu____17611 -> lopt

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
            (let uu____17632 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17633 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17632
               uu____17633)
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
          let uu____17653 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17653
          then tm1
          else
            (let w t =
               let uu___203_17667 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___203_17667.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___203_17667.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17678 =
                 let uu____17679 = FStar_Syntax_Util.unmeta t  in
                 uu____17679.FStar_Syntax_Syntax.n  in
               match uu____17678 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17686 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17735)::args1,(bv,uu____17738)::bs1) ->
                   let uu____17772 =
                     let uu____17773 = FStar_Syntax_Subst.compress t  in
                     uu____17773.FStar_Syntax_Syntax.n  in
                   (match uu____17772 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17777 -> false)
               | ([],[]) -> true
               | (uu____17798,uu____17799) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17840 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17841 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17840
                    uu____17841)
               else ();
               (let uu____17843 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17843 with
                | (hd1,args) ->
                    let uu____17876 =
                      let uu____17877 = FStar_Syntax_Subst.compress hd1  in
                      uu____17877.FStar_Syntax_Syntax.n  in
                    (match uu____17876 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____17884 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17885 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17886 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17884 uu____17885 uu____17886)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17888 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17905 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17906 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17905
                    uu____17906)
               else ();
               (let uu____17908 = FStar_Syntax_Util.is_squash t  in
                match uu____17908 with
                | FStar_Pervasives_Native.Some (uu____17919,t') ->
                    is_applied bs t'
                | uu____17931 ->
                    let uu____17940 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17940 with
                     | FStar_Pervasives_Native.Some (uu____17951,t') ->
                         is_applied bs t'
                     | uu____17963 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17987 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17987 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17994)::(q,uu____17996)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18032 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18033 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18032 uu____18033)
                    else ();
                    (let uu____18035 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18035 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18040 =
                           let uu____18041 = FStar_Syntax_Subst.compress p
                              in
                           uu____18041.FStar_Syntax_Syntax.n  in
                         (match uu____18040 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18049 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18049))
                          | uu____18050 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18053)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18078 =
                           let uu____18079 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18079.FStar_Syntax_Syntax.n  in
                         (match uu____18078 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18087 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18087))
                          | uu____18088 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18092 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18092 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18097 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18097 with
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
                                     let uu____18106 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18106))
                               | uu____18107 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18112)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18137 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18137 with
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
                                     let uu____18146 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18146))
                               | uu____18147 -> FStar_Pervasives_Native.None)
                          | uu____18150 -> FStar_Pervasives_Native.None)
                     | uu____18153 -> FStar_Pervasives_Native.None))
               | uu____18156 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18169 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18169 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18175)::[],uu____18176,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18193 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18194 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18193
                         uu____18194)
                    else ();
                    is_quantified_const bv phi')
               | uu____18196 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18209 =
                 let uu____18210 = FStar_Syntax_Subst.compress phi  in
                 uu____18210.FStar_Syntax_Syntax.n  in
               match uu____18209 with
               | FStar_Syntax_Syntax.Tm_match (uu____18215,br::brs) ->
                   let uu____18282 = br  in
                   (match uu____18282 with
                    | (uu____18299,uu____18300,e) ->
                        let r =
                          let uu____18321 = simp_t e  in
                          match uu____18321 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18327 =
                                FStar_List.for_all
                                  (fun uu____18345  ->
                                     match uu____18345 with
                                     | (uu____18358,uu____18359,e') ->
                                         let uu____18373 = simp_t e'  in
                                         uu____18373 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18327
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18381 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18388 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18388
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18413 =
                 match uu____18413 with
                 | (t1,q) ->
                     let uu____18426 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18426 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18454 -> (t1, q))
                  in
               let uu____18463 = FStar_Syntax_Util.head_and_args t  in
               match uu____18463 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18527 =
                 let uu____18528 = FStar_Syntax_Util.unmeta ty  in
                 uu____18528.FStar_Syntax_Syntax.n  in
               match uu____18527 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18532) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18537,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18557 -> false  in
             let simplify1 arg =
               let uu____18582 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18582, arg)  in
             let uu____18591 = is_forall_const tm1  in
             match uu____18591 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____18596 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18597 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18596
                       uu____18597)
                  else ();
                  (let uu____18599 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18599))
             | FStar_Pervasives_Native.None  ->
                 let uu____18600 =
                   let uu____18601 = FStar_Syntax_Subst.compress tm1  in
                   uu____18601.FStar_Syntax_Syntax.n  in
                 (match uu____18600 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18605;
                              FStar_Syntax_Syntax.vars = uu____18606;_},uu____18607);
                         FStar_Syntax_Syntax.pos = uu____18608;
                         FStar_Syntax_Syntax.vars = uu____18609;_},args)
                      ->
                      let uu____18635 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18635
                      then
                        let uu____18636 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18636 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18683)::
                             (uu____18684,(arg,uu____18686))::[] ->
                             maybe_auto_squash arg
                         | (uu____18735,(arg,uu____18737))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18738)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18787)::uu____18788::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18839::(FStar_Pervasives_Native.Some (false
                                         ),uu____18840)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18891 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18905 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18905
                         then
                           let uu____18906 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18906 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18953)::uu____18954::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19005::(FStar_Pervasives_Native.Some (true
                                           ),uu____19006)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19057)::(uu____19058,(arg,uu____19060))::[]
                               -> maybe_auto_squash arg
                           | (uu____19109,(arg,uu____19111))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19112)::[]
                               -> maybe_auto_squash arg
                           | uu____19161 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19175 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19175
                            then
                              let uu____19176 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19176 with
                              | uu____19223::(FStar_Pervasives_Native.Some
                                              (true ),uu____19224)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19275)::uu____19276::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19327)::(uu____19328,(arg,uu____19330))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19379,(p,uu____19381))::(uu____19382,
                                                                (q,uu____19384))::[]
                                  ->
                                  let uu____19431 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19431
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19433 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19447 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19447
                               then
                                 let uu____19448 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19448 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19495)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19496)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19547)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19548)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19599)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19600)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19651)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19652)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19703,(arg,uu____19705))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19706)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19755)::(uu____19756,(arg,uu____19758))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19807,(arg,uu____19809))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19810)::[]
                                     ->
                                     let uu____19859 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19859
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19860)::(uu____19861,(arg,uu____19863))::[]
                                     ->
                                     let uu____19912 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19912
                                 | (uu____19913,(p,uu____19915))::(uu____19916,
                                                                   (q,uu____19918))::[]
                                     ->
                                     let uu____19965 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19965
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19967 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19981 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19981
                                  then
                                    let uu____19982 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19982 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20029)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20060)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20091 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20105 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20105
                                     then
                                       match args with
                                       | (t,uu____20107)::[] ->
                                           let uu____20124 =
                                             let uu____20125 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20125.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20124 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20128::[],body,uu____20130)
                                                ->
                                                let uu____20157 = simp_t body
                                                   in
                                                (match uu____20157 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20160 -> tm1)
                                            | uu____20163 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20165))::(t,uu____20167)::[]
                                           ->
                                           let uu____20206 =
                                             let uu____20207 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20207.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20206 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20210::[],body,uu____20212)
                                                ->
                                                let uu____20239 = simp_t body
                                                   in
                                                (match uu____20239 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20242 -> tm1)
                                            | uu____20245 -> tm1)
                                       | uu____20246 -> tm1
                                     else
                                       (let uu____20256 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20256
                                        then
                                          match args with
                                          | (t,uu____20258)::[] ->
                                              let uu____20275 =
                                                let uu____20276 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20276.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20275 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20279::[],body,uu____20281)
                                                   ->
                                                   let uu____20308 =
                                                     simp_t body  in
                                                   (match uu____20308 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20311 -> tm1)
                                               | uu____20314 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20316))::(t,uu____20318)::[]
                                              ->
                                              let uu____20357 =
                                                let uu____20358 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20358.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20357 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20361::[],body,uu____20363)
                                                   ->
                                                   let uu____20390 =
                                                     simp_t body  in
                                                   (match uu____20390 with
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
                                                    | uu____20393 -> tm1)
                                               | uu____20396 -> tm1)
                                          | uu____20397 -> tm1
                                        else
                                          (let uu____20407 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20407
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20408;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20409;_},uu____20410)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20427;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20428;_},uu____20429)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20446 -> tm1
                                           else
                                             (let uu____20456 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20456 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20476 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20486;
                         FStar_Syntax_Syntax.vars = uu____20487;_},args)
                      ->
                      let uu____20509 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20509
                      then
                        let uu____20510 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20510 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20557)::
                             (uu____20558,(arg,uu____20560))::[] ->
                             maybe_auto_squash arg
                         | (uu____20609,(arg,uu____20611))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20612)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20661)::uu____20662::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20713::(FStar_Pervasives_Native.Some (false
                                         ),uu____20714)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20765 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20779 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20779
                         then
                           let uu____20780 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20780 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20827)::uu____20828::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20879::(FStar_Pervasives_Native.Some (true
                                           ),uu____20880)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20931)::(uu____20932,(arg,uu____20934))::[]
                               -> maybe_auto_squash arg
                           | (uu____20983,(arg,uu____20985))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20986)::[]
                               -> maybe_auto_squash arg
                           | uu____21035 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21049 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21049
                            then
                              let uu____21050 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21050 with
                              | uu____21097::(FStar_Pervasives_Native.Some
                                              (true ),uu____21098)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21149)::uu____21150::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21201)::(uu____21202,(arg,uu____21204))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21253,(p,uu____21255))::(uu____21256,
                                                                (q,uu____21258))::[]
                                  ->
                                  let uu____21305 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21305
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21307 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21321 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21321
                               then
                                 let uu____21322 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21322 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21369)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21370)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21421)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21422)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21473)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21474)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21525)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21526)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21577,(arg,uu____21579))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21580)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21629)::(uu____21630,(arg,uu____21632))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21681,(arg,uu____21683))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21684)::[]
                                     ->
                                     let uu____21733 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21733
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21734)::(uu____21735,(arg,uu____21737))::[]
                                     ->
                                     let uu____21786 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21786
                                 | (uu____21787,(p,uu____21789))::(uu____21790,
                                                                   (q,uu____21792))::[]
                                     ->
                                     let uu____21839 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21839
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21841 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21855 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21855
                                  then
                                    let uu____21856 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21856 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21903)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21934)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21965 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21979 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21979
                                     then
                                       match args with
                                       | (t,uu____21981)::[] ->
                                           let uu____21998 =
                                             let uu____21999 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21999.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21998 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22002::[],body,uu____22004)
                                                ->
                                                let uu____22031 = simp_t body
                                                   in
                                                (match uu____22031 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22034 -> tm1)
                                            | uu____22037 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22039))::(t,uu____22041)::[]
                                           ->
                                           let uu____22080 =
                                             let uu____22081 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22081.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22080 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22084::[],body,uu____22086)
                                                ->
                                                let uu____22113 = simp_t body
                                                   in
                                                (match uu____22113 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22116 -> tm1)
                                            | uu____22119 -> tm1)
                                       | uu____22120 -> tm1
                                     else
                                       (let uu____22130 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22130
                                        then
                                          match args with
                                          | (t,uu____22132)::[] ->
                                              let uu____22149 =
                                                let uu____22150 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22150.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22149 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22153::[],body,uu____22155)
                                                   ->
                                                   let uu____22182 =
                                                     simp_t body  in
                                                   (match uu____22182 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22185 -> tm1)
                                               | uu____22188 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22190))::(t,uu____22192)::[]
                                              ->
                                              let uu____22231 =
                                                let uu____22232 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22232.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22231 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22235::[],body,uu____22237)
                                                   ->
                                                   let uu____22264 =
                                                     simp_t body  in
                                                   (match uu____22264 with
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
                                                    | uu____22267 -> tm1)
                                               | uu____22270 -> tm1)
                                          | uu____22271 -> tm1
                                        else
                                          (let uu____22281 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22281
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22282;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22283;_},uu____22284)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22301;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22302;_},uu____22303)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22320 -> tm1
                                           else
                                             (let uu____22330 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22330 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22350 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22365 = simp_t t  in
                      (match uu____22365 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22368 ->
                      let uu____22391 = is_const_match tm1  in
                      (match uu____22391 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22394 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22404  ->
               (let uu____22406 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22407 = FStar_Syntax_Print.term_to_string t  in
                let uu____22408 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22415 =
                  let uu____22416 =
                    let uu____22419 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22419
                     in
                  stack_to_string uu____22416  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22406 uu____22407 uu____22408 uu____22415);
               (let uu____22442 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22442
                then
                  let uu____22443 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22443 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22450 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22451 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22452 =
                          let uu____22453 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22453
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22450
                          uu____22451 uu____22452);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22471 =
                     let uu____22472 =
                       let uu____22473 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22473  in
                     FStar_Util.string_of_int uu____22472  in
                   let uu____22478 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22479 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22471 uu____22478 uu____22479)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22485,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22534  ->
                     let uu____22535 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22535);
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
               let uu____22571 =
                 let uu___204_22572 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___204_22572.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___204_22572.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22571
           | (Arg (Univ uu____22573,uu____22574,uu____22575))::uu____22576 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22579,uu____22580))::uu____22581 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22596,uu____22597),aq,r))::stack1
               when
               let uu____22647 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22647 ->
               let t2 =
                 let uu____22651 =
                   let uu____22656 =
                     let uu____22657 = closure_as_term cfg env_arg tm  in
                     (uu____22657, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22656  in
                 uu____22651 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22663),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22716  ->
                     let uu____22717 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22717);
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
                   (let uu____22728 = FStar_ST.op_Bang m  in
                    match uu____22728 with
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
                    | FStar_Pervasives_Native.Some (uu____22869,a) ->
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (a, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env_arg stack1 t2)))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22920 =
                 log cfg
                   (fun uu____22924  ->
                      let uu____22925 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22925);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22929 =
                 let uu____22930 = FStar_Syntax_Subst.compress t1  in
                 uu____22930.FStar_Syntax_Syntax.n  in
               (match uu____22929 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22957 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22957  in
                    (log cfg
                       (fun uu____22961  ->
                          let uu____22962 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22962);
                     (let uu____22963 = FStar_List.tl stack  in
                      norm cfg env1 uu____22963 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22964);
                       FStar_Syntax_Syntax.pos = uu____22965;
                       FStar_Syntax_Syntax.vars = uu____22966;_},(e,uu____22968)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22997 when
                    (cfg.steps).primops ->
                    let uu____23012 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23012 with
                     | (hd1,args) ->
                         let uu____23049 =
                           let uu____23050 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23050.FStar_Syntax_Syntax.n  in
                         (match uu____23049 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23054 = find_prim_step cfg fv  in
                              (match uu____23054 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23057; arity = uu____23058;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23060;
                                     requires_binder_substitution =
                                       uu____23061;
                                     interpretation = uu____23062;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23077 -> fallback " (3)" ())
                          | uu____23080 -> fallback " (4)" ()))
                | uu____23081 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23102  ->
                     let uu____23103 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23103);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23112 =
                   log cfg1
                     (fun uu____23117  ->
                        let uu____23118 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23119 =
                          let uu____23120 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23137  ->
                                    match uu____23137 with
                                    | (p,uu____23147,uu____23148) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23120
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23118 uu____23119);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___113_23165  ->
                                match uu___113_23165 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23166 -> false))
                         in
                      let steps =
                        let uu___205_23168 = cfg1.steps  in
                        {
                          beta = (uu___205_23168.beta);
                          iota = (uu___205_23168.iota);
                          zeta = false;
                          weak = (uu___205_23168.weak);
                          hnf = (uu___205_23168.hnf);
                          primops = (uu___205_23168.primops);
                          do_not_unfold_pure_lets =
                            (uu___205_23168.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___205_23168.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___205_23168.pure_subterms_within_computations);
                          simplify = (uu___205_23168.simplify);
                          erase_universes = (uu___205_23168.erase_universes);
                          allow_unbound_universes =
                            (uu___205_23168.allow_unbound_universes);
                          reify_ = (uu___205_23168.reify_);
                          compress_uvars = (uu___205_23168.compress_uvars);
                          no_full_norm = (uu___205_23168.no_full_norm);
                          check_no_uvars = (uu___205_23168.check_no_uvars);
                          unmeta = (uu___205_23168.unmeta);
                          unascribe = (uu___205_23168.unascribe);
                          in_full_norm_request =
                            (uu___205_23168.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___205_23168.weakly_reduce_scrutinee)
                        }  in
                      let uu___206_23173 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___206_23173.tcenv);
                        debug = (uu___206_23173.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___206_23173.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___206_23173.memoize_lazy);
                        normalize_pure_lets =
                          (uu___206_23173.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23213 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23234 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23294  ->
                                    fun uu____23295  ->
                                      match (uu____23294, uu____23295) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23386 = norm_pat env3 p1
                                             in
                                          (match uu____23386 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23234 with
                           | (pats1,env3) ->
                               ((let uu___207_23468 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___207_23468.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___208_23487 = x  in
                            let uu____23488 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___208_23487.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___208_23487.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23488
                            }  in
                          ((let uu___209_23502 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___209_23502.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___210_23513 = x  in
                            let uu____23514 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___210_23513.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___210_23513.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23514
                            }  in
                          ((let uu___211_23528 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___211_23528.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___212_23544 = x  in
                            let uu____23545 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___212_23544.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___212_23544.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23545
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___213_23552 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___213_23552.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23562 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23576 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23576 with
                                  | (p,wopt,e) ->
                                      let uu____23596 = norm_pat env1 p  in
                                      (match uu____23596 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23621 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23621
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23628 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23628
                      then
                        norm
                          (let uu___214_23631 = cfg1  in
                           {
                             steps =
                               (let uu___215_23634 = cfg1.steps  in
                                {
                                  beta = (uu___215_23634.beta);
                                  iota = (uu___215_23634.iota);
                                  zeta = (uu___215_23634.zeta);
                                  weak = (uu___215_23634.weak);
                                  hnf = (uu___215_23634.hnf);
                                  primops = (uu___215_23634.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___215_23634.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___215_23634.unfold_until);
                                  unfold_only = (uu___215_23634.unfold_only);
                                  unfold_fully =
                                    (uu___215_23634.unfold_fully);
                                  unfold_attr = (uu___215_23634.unfold_attr);
                                  unfold_tac = (uu___215_23634.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___215_23634.pure_subterms_within_computations);
                                  simplify = (uu___215_23634.simplify);
                                  erase_universes =
                                    (uu___215_23634.erase_universes);
                                  allow_unbound_universes =
                                    (uu___215_23634.allow_unbound_universes);
                                  reify_ = (uu___215_23634.reify_);
                                  compress_uvars =
                                    (uu___215_23634.compress_uvars);
                                  no_full_norm =
                                    (uu___215_23634.no_full_norm);
                                  check_no_uvars =
                                    (uu___215_23634.check_no_uvars);
                                  unmeta = (uu___215_23634.unmeta);
                                  unascribe = (uu___215_23634.unascribe);
                                  in_full_norm_request =
                                    (uu___215_23634.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___214_23631.tcenv);
                             debug = (uu___214_23631.debug);
                             delta_level = (uu___214_23631.delta_level);
                             primitive_steps =
                               (uu___214_23631.primitive_steps);
                             strong = (uu___214_23631.strong);
                             memoize_lazy = (uu___214_23631.memoize_lazy);
                             normalize_pure_lets =
                               (uu___214_23631.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23636 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23636)
                    in
                 let rec is_cons head1 =
                   let uu____23643 =
                     let uu____23644 = FStar_Syntax_Subst.compress head1  in
                     uu____23644.FStar_Syntax_Syntax.n  in
                   match uu____23643 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23648) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23653 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23654;
                         FStar_Syntax_Syntax.fv_delta = uu____23655;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23656;
                         FStar_Syntax_Syntax.fv_delta = uu____23657;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23658);_}
                       -> true
                   | uu____23665 -> false  in
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
                   let uu____23826 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23826 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23913 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23952 ->
                                 let uu____23953 =
                                   let uu____23954 = is_cons head1  in
                                   Prims.op_Negation uu____23954  in
                                 FStar_Util.Inr uu____23953)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23979 =
                              let uu____23980 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23980.FStar_Syntax_Syntax.n  in
                            (match uu____23979 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23998 ->
                                 let uu____23999 =
                                   let uu____24000 = is_cons head1  in
                                   Prims.op_Negation uu____24000  in
                                 FStar_Util.Inr uu____23999))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24069)::rest_a,(p1,uu____24072)::rest_p) ->
                       let uu____24116 = matches_pat t2 p1  in
                       (match uu____24116 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24165 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24275 = matches_pat scrutinee1 p1  in
                       (match uu____24275 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24315  ->
                                  let uu____24316 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24317 =
                                    let uu____24318 =
                                      FStar_List.map
                                        (fun uu____24328  ->
                                           match uu____24328 with
                                           | (uu____24333,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24318
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24316 uu____24317);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24365  ->
                                       match uu____24365 with
                                       | (bv,t2) ->
                                           let uu____24388 =
                                             let uu____24395 =
                                               let uu____24398 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24398
                                                in
                                             let uu____24399 =
                                               let uu____24400 =
                                                 let uu____24431 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24431, false)
                                                  in
                                               Clos uu____24400  in
                                             (uu____24395, uu____24399)  in
                                           uu____24388 :: env2) env1 s
                                 in
                              let uu____24548 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24548)))
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
    let uu____24575 =
      let uu____24578 = FStar_ST.op_Bang plugins  in p :: uu____24578  in
    FStar_ST.op_Colon_Equals plugins uu____24575  in
  let retrieve uu____24686 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24763  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___114_24804  ->
                  match uu___114_24804 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24808 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24814 -> d  in
        let uu____24817 = to_fsteps s  in
        let uu____24818 =
          let uu____24819 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24820 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24821 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24822 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____24823 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24824 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24819;
            primop = uu____24820;
            b380 = uu____24821;
            wpe = uu____24822;
            norm_delayed = uu____24823;
            print_normalized = uu____24824
          }  in
        let uu____24825 =
          let uu____24828 =
            let uu____24831 = retrieve_plugins ()  in
            FStar_List.append uu____24831 psteps  in
          add_steps built_in_primitive_steps uu____24828  in
        let uu____24834 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24836 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24836)
           in
        {
          steps = uu____24817;
          tcenv = e;
          debug = uu____24818;
          delta_level = d1;
          primitive_steps = uu____24825;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24834
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
      fun t  -> let uu____24918 = config s e  in norm_comp uu____24918 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24935 = config [] env  in norm_universe uu____24935 [] u
  
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
        let uu____24959 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24959  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24966 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___216_24985 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___216_24985.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___216_24985.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24992 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24992
          then
            let ct1 =
              let uu____24994 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24994 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____25001 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25001
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___217_25005 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___217_25005.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___217_25005.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___217_25005.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___218_25007 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___218_25007.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___218_25007.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___218_25007.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___218_25007.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___219_25008 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___219_25008.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___219_25008.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25010 -> c
  
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
        let uu____25028 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25028  in
      let uu____25035 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25035
      then
        let uu____25036 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25036 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25042  ->
                 let uu____25043 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25043)
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
            ((let uu____25064 =
                let uu____25069 =
                  let uu____25070 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25070
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25069)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25064);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25085 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25085 [] c
        with
        | e ->
            ((let uu____25098 =
                let uu____25103 =
                  let uu____25104 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25104
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25103)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25098);
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
                   let uu____25149 =
                     let uu____25150 =
                       let uu____25157 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25157)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25150  in
                   mk uu____25149 t01.FStar_Syntax_Syntax.pos
               | uu____25162 -> t2)
          | uu____25163 -> t2  in
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
        let uu____25227 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25227 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25256 ->
                 let uu____25263 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25263 with
                  | (actuals,uu____25273,uu____25274) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25288 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25288 with
                         | (binders,args) ->
                             let uu____25305 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25305
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
      | uu____25317 ->
          let uu____25318 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25318 with
           | (head1,args) ->
               let uu____25355 =
                 let uu____25356 = FStar_Syntax_Subst.compress head1  in
                 uu____25356.FStar_Syntax_Syntax.n  in
               (match uu____25355 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25359,thead) ->
                    let uu____25385 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25385 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25427 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___224_25435 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___224_25435.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___224_25435.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___224_25435.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___224_25435.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___224_25435.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___224_25435.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___224_25435.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___224_25435.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___224_25435.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___224_25435.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___224_25435.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___224_25435.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___224_25435.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___224_25435.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___224_25435.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___224_25435.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___224_25435.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___224_25435.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___224_25435.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___224_25435.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___224_25435.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___224_25435.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___224_25435.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___224_25435.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___224_25435.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___224_25435.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___224_25435.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___224_25435.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___224_25435.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___224_25435.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___224_25435.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___224_25435.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___224_25435.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___224_25435.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25427 with
                            | (uu____25436,ty,uu____25438) ->
                                eta_expand_with_type env t ty))
                | uu____25439 ->
                    let uu____25440 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___225_25448 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___225_25448.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___225_25448.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___225_25448.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___225_25448.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___225_25448.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___225_25448.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___225_25448.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___225_25448.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___225_25448.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___225_25448.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___225_25448.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___225_25448.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___225_25448.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___225_25448.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___225_25448.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___225_25448.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___225_25448.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___225_25448.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___225_25448.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___225_25448.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___225_25448.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___225_25448.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___225_25448.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___225_25448.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___225_25448.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___225_25448.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___225_25448.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___225_25448.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___225_25448.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___225_25448.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___225_25448.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___225_25448.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___225_25448.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___225_25448.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25440 with
                     | (uu____25449,ty,uu____25451) ->
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
      let uu___226_25524 = x  in
      let uu____25525 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___226_25524.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___226_25524.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25525
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25528 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25553 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25554 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25555 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25556 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25563 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25564 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25565 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___227_25595 = rc  in
          let uu____25596 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25603 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___227_25595.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25596;
            FStar_Syntax_Syntax.residual_flags = uu____25603
          }  in
        let uu____25606 =
          let uu____25607 =
            let uu____25624 = elim_delayed_subst_binders bs  in
            let uu____25631 = elim_delayed_subst_term t2  in
            let uu____25632 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25624, uu____25631, uu____25632)  in
          FStar_Syntax_Syntax.Tm_abs uu____25607  in
        mk1 uu____25606
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25661 =
          let uu____25662 =
            let uu____25675 = elim_delayed_subst_binders bs  in
            let uu____25682 = elim_delayed_subst_comp c  in
            (uu____25675, uu____25682)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25662  in
        mk1 uu____25661
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25695 =
          let uu____25696 =
            let uu____25703 = elim_bv bv  in
            let uu____25704 = elim_delayed_subst_term phi  in
            (uu____25703, uu____25704)  in
          FStar_Syntax_Syntax.Tm_refine uu____25696  in
        mk1 uu____25695
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25727 =
          let uu____25728 =
            let uu____25743 = elim_delayed_subst_term t2  in
            let uu____25744 = elim_delayed_subst_args args  in
            (uu____25743, uu____25744)  in
          FStar_Syntax_Syntax.Tm_app uu____25728  in
        mk1 uu____25727
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___228_25810 = p  in
              let uu____25811 =
                let uu____25812 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25812  in
              {
                FStar_Syntax_Syntax.v = uu____25811;
                FStar_Syntax_Syntax.p =
                  (uu___228_25810.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___229_25814 = p  in
              let uu____25815 =
                let uu____25816 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25816  in
              {
                FStar_Syntax_Syntax.v = uu____25815;
                FStar_Syntax_Syntax.p =
                  (uu___229_25814.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___230_25823 = p  in
              let uu____25824 =
                let uu____25825 =
                  let uu____25832 = elim_bv x  in
                  let uu____25833 = elim_delayed_subst_term t0  in
                  (uu____25832, uu____25833)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25825  in
              {
                FStar_Syntax_Syntax.v = uu____25824;
                FStar_Syntax_Syntax.p =
                  (uu___230_25823.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___231_25852 = p  in
              let uu____25853 =
                let uu____25854 =
                  let uu____25867 =
                    FStar_List.map
                      (fun uu____25890  ->
                         match uu____25890 with
                         | (x,b) ->
                             let uu____25903 = elim_pat x  in
                             (uu____25903, b)) pats
                     in
                  (fv, uu____25867)  in
                FStar_Syntax_Syntax.Pat_cons uu____25854  in
              {
                FStar_Syntax_Syntax.v = uu____25853;
                FStar_Syntax_Syntax.p =
                  (uu___231_25852.FStar_Syntax_Syntax.p)
              }
          | uu____25916 -> p  in
        let elim_branch uu____25940 =
          match uu____25940 with
          | (pat,wopt,t3) ->
              let uu____25966 = elim_pat pat  in
              let uu____25969 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25972 = elim_delayed_subst_term t3  in
              (uu____25966, uu____25969, uu____25972)
           in
        let uu____25977 =
          let uu____25978 =
            let uu____26001 = elim_delayed_subst_term t2  in
            let uu____26002 = FStar_List.map elim_branch branches  in
            (uu____26001, uu____26002)  in
          FStar_Syntax_Syntax.Tm_match uu____25978  in
        mk1 uu____25977
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26113 =
          match uu____26113 with
          | (tc,topt) ->
              let uu____26148 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26158 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26158
                | FStar_Util.Inr c ->
                    let uu____26160 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26160
                 in
              let uu____26161 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26148, uu____26161)
           in
        let uu____26170 =
          let uu____26171 =
            let uu____26198 = elim_delayed_subst_term t2  in
            let uu____26199 = elim_ascription a  in
            (uu____26198, uu____26199, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26171  in
        mk1 uu____26170
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___232_26246 = lb  in
          let uu____26247 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26250 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___232_26246.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___232_26246.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26247;
            FStar_Syntax_Syntax.lbeff =
              (uu___232_26246.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26250;
            FStar_Syntax_Syntax.lbattrs =
              (uu___232_26246.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___232_26246.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26253 =
          let uu____26254 =
            let uu____26267 =
              let uu____26274 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26274)  in
            let uu____26283 = elim_delayed_subst_term t2  in
            (uu____26267, uu____26283)  in
          FStar_Syntax_Syntax.Tm_let uu____26254  in
        mk1 uu____26253
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26316 =
          let uu____26317 =
            let uu____26334 = elim_delayed_subst_term t2  in
            (uv, uu____26334)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26317  in
        mk1 uu____26316
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26352 =
          let uu____26353 =
            let uu____26360 = elim_delayed_subst_term tm  in
            (uu____26360, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26353  in
        mk1 uu____26352
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26367 =
          let uu____26368 =
            let uu____26375 = elim_delayed_subst_term t2  in
            let uu____26376 = elim_delayed_subst_meta md  in
            (uu____26375, uu____26376)  in
          FStar_Syntax_Syntax.Tm_meta uu____26368  in
        mk1 uu____26367

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___115_26383  ->
         match uu___115_26383 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26387 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26387
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
        let uu____26410 =
          let uu____26411 =
            let uu____26420 = elim_delayed_subst_term t  in
            (uu____26420, uopt)  in
          FStar_Syntax_Syntax.Total uu____26411  in
        mk1 uu____26410
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26433 =
          let uu____26434 =
            let uu____26443 = elim_delayed_subst_term t  in
            (uu____26443, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26434  in
        mk1 uu____26433
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___233_26448 = ct  in
          let uu____26449 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26452 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26461 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___233_26448.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___233_26448.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26449;
            FStar_Syntax_Syntax.effect_args = uu____26452;
            FStar_Syntax_Syntax.flags = uu____26461
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___116_26464  ->
    match uu___116_26464 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26476 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26476
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26509 =
          let uu____26516 = elim_delayed_subst_term t  in (m, uu____26516)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26509
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26524 =
          let uu____26533 = elim_delayed_subst_term t  in
          (m1, m2, uu____26533)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26524
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26556  ->
         match uu____26556 with
         | (t,q) ->
             let uu____26567 = elim_delayed_subst_term t  in (uu____26567, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26587  ->
         match uu____26587 with
         | (x,q) ->
             let uu____26598 =
               let uu___234_26599 = x  in
               let uu____26600 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___234_26599.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___234_26599.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26600
               }  in
             (uu____26598, q)) bs

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
            | (uu____26684,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26690,FStar_Util.Inl t) ->
                let uu____26696 =
                  let uu____26703 =
                    let uu____26704 =
                      let uu____26717 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26717)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26704  in
                  FStar_Syntax_Syntax.mk uu____26703  in
                uu____26696 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26721 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26721 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26749 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26804 ->
                    let uu____26805 =
                      let uu____26814 =
                        let uu____26815 = FStar_Syntax_Subst.compress t4  in
                        uu____26815.FStar_Syntax_Syntax.n  in
                      (uu____26814, tc)  in
                    (match uu____26805 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26840) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26877) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26916,FStar_Util.Inl uu____26917) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26940 -> failwith "Impossible")
                 in
              (match uu____26749 with
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
          let uu____27053 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____27053 with
          | (univ_names1,binders1,tc) ->
              let uu____27111 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____27111)
  
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
          let uu____27154 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____27154 with
          | (univ_names1,binders1,tc) ->
              let uu____27214 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27214)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27251 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27251 with
           | (univ_names1,binders1,typ1) ->
               let uu___235_27279 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___235_27279.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___235_27279.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___235_27279.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___235_27279.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___236_27300 = s  in
          let uu____27301 =
            let uu____27302 =
              let uu____27311 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27311, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27302  in
          {
            FStar_Syntax_Syntax.sigel = uu____27301;
            FStar_Syntax_Syntax.sigrng =
              (uu___236_27300.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___236_27300.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___236_27300.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___236_27300.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27328 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27328 with
           | (univ_names1,uu____27346,typ1) ->
               let uu___237_27360 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___237_27360.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___237_27360.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___237_27360.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___237_27360.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27366 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27366 with
           | (univ_names1,uu____27384,typ1) ->
               let uu___238_27398 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___238_27398.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___238_27398.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___238_27398.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___238_27398.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27432 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27432 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27457 =
                            let uu____27458 =
                              let uu____27459 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27459  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27458
                             in
                          elim_delayed_subst_term uu____27457  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___239_27462 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___239_27462.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___239_27462.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___239_27462.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___239_27462.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___240_27463 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___240_27463.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___240_27463.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___240_27463.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___240_27463.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___241_27475 = s  in
          let uu____27476 =
            let uu____27477 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27477  in
          {
            FStar_Syntax_Syntax.sigel = uu____27476;
            FStar_Syntax_Syntax.sigrng =
              (uu___241_27475.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___241_27475.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___241_27475.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___241_27475.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27481 = elim_uvars_aux_t env us [] t  in
          (match uu____27481 with
           | (us1,uu____27499,t1) ->
               let uu___242_27513 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_27513.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_27513.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_27513.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_27513.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27514 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27516 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27516 with
           | (univs1,binders,signature) ->
               let uu____27544 =
                 let uu____27553 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27553 with
                 | (univs_opening,univs2) ->
                     let uu____27580 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27580)
                  in
               (match uu____27544 with
                | (univs_opening,univs_closing) ->
                    let uu____27597 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27603 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27604 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27603, uu____27604)  in
                    (match uu____27597 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27628 =
                           match uu____27628 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27646 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27646 with
                                | (us1,t1) ->
                                    let uu____27657 =
                                      let uu____27662 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27669 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27662, uu____27669)  in
                                    (match uu____27657 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27682 =
                                           let uu____27687 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27696 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27687, uu____27696)  in
                                         (match uu____27682 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27712 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27712
                                                 in
                                              let uu____27713 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27713 with
                                               | (uu____27734,uu____27735,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27750 =
                                                       let uu____27751 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27751
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27750
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27758 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27758 with
                           | (uu____27771,uu____27772,t1) -> t1  in
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
                             | uu____27834 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27853 =
                               let uu____27854 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27854.FStar_Syntax_Syntax.n  in
                             match uu____27853 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27913 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27944 =
                               let uu____27945 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27945.FStar_Syntax_Syntax.n  in
                             match uu____27944 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27966) ->
                                 let uu____27987 = destruct_action_body body
                                    in
                                 (match uu____27987 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____28032 ->
                                 let uu____28033 = destruct_action_body t  in
                                 (match uu____28033 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____28082 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____28082 with
                           | (action_univs,t) ->
                               let uu____28091 = destruct_action_typ_templ t
                                  in
                               (match uu____28091 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___243_28132 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___243_28132.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___243_28132.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___244_28134 = ed  in
                           let uu____28135 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____28136 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____28137 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____28138 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____28139 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____28140 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____28141 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____28142 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____28143 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____28144 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____28145 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____28146 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____28147 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____28148 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___244_28134.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___244_28134.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____28135;
                             FStar_Syntax_Syntax.bind_wp = uu____28136;
                             FStar_Syntax_Syntax.if_then_else = uu____28137;
                             FStar_Syntax_Syntax.ite_wp = uu____28138;
                             FStar_Syntax_Syntax.stronger = uu____28139;
                             FStar_Syntax_Syntax.close_wp = uu____28140;
                             FStar_Syntax_Syntax.assert_p = uu____28141;
                             FStar_Syntax_Syntax.assume_p = uu____28142;
                             FStar_Syntax_Syntax.null_wp = uu____28143;
                             FStar_Syntax_Syntax.trivial = uu____28144;
                             FStar_Syntax_Syntax.repr = uu____28145;
                             FStar_Syntax_Syntax.return_repr = uu____28146;
                             FStar_Syntax_Syntax.bind_repr = uu____28147;
                             FStar_Syntax_Syntax.actions = uu____28148;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___244_28134.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___245_28151 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___245_28151.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___245_28151.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___245_28151.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___245_28151.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___117_28170 =
            match uu___117_28170 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28197 = elim_uvars_aux_t env us [] t  in
                (match uu____28197 with
                 | (us1,uu____28221,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___246_28240 = sub_eff  in
            let uu____28241 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28244 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___246_28240.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___246_28240.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28241;
              FStar_Syntax_Syntax.lift = uu____28244
            }  in
          let uu___247_28247 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___247_28247.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___247_28247.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___247_28247.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___247_28247.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28257 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28257 with
           | (univ_names1,binders1,comp1) ->
               let uu___248_28291 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_28291.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_28291.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_28291.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_28291.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28302 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28303 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  