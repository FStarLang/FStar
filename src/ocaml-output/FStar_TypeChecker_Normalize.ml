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
      fun uu___239_269  ->
        match uu___239_269 with
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
      let add_opt x uu___240_1503 =
        match uu___240_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___259_1523 = fs  in
          {
            beta = true;
            iota = (uu___259_1523.iota);
            zeta = (uu___259_1523.zeta);
            weak = (uu___259_1523.weak);
            hnf = (uu___259_1523.hnf);
            primops = (uu___259_1523.primops);
            do_not_unfold_pure_lets = (uu___259_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___259_1523.unfold_until);
            unfold_only = (uu___259_1523.unfold_only);
            unfold_fully = (uu___259_1523.unfold_fully);
            unfold_attr = (uu___259_1523.unfold_attr);
            unfold_tac = (uu___259_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___259_1523.pure_subterms_within_computations);
            simplify = (uu___259_1523.simplify);
            erase_universes = (uu___259_1523.erase_universes);
            allow_unbound_universes = (uu___259_1523.allow_unbound_universes);
            reify_ = (uu___259_1523.reify_);
            compress_uvars = (uu___259_1523.compress_uvars);
            no_full_norm = (uu___259_1523.no_full_norm);
            check_no_uvars = (uu___259_1523.check_no_uvars);
            unmeta = (uu___259_1523.unmeta);
            unascribe = (uu___259_1523.unascribe);
            in_full_norm_request = (uu___259_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___259_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___260_1524 = fs  in
          {
            beta = (uu___260_1524.beta);
            iota = true;
            zeta = (uu___260_1524.zeta);
            weak = (uu___260_1524.weak);
            hnf = (uu___260_1524.hnf);
            primops = (uu___260_1524.primops);
            do_not_unfold_pure_lets = (uu___260_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___260_1524.unfold_until);
            unfold_only = (uu___260_1524.unfold_only);
            unfold_fully = (uu___260_1524.unfold_fully);
            unfold_attr = (uu___260_1524.unfold_attr);
            unfold_tac = (uu___260_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___260_1524.pure_subterms_within_computations);
            simplify = (uu___260_1524.simplify);
            erase_universes = (uu___260_1524.erase_universes);
            allow_unbound_universes = (uu___260_1524.allow_unbound_universes);
            reify_ = (uu___260_1524.reify_);
            compress_uvars = (uu___260_1524.compress_uvars);
            no_full_norm = (uu___260_1524.no_full_norm);
            check_no_uvars = (uu___260_1524.check_no_uvars);
            unmeta = (uu___260_1524.unmeta);
            unascribe = (uu___260_1524.unascribe);
            in_full_norm_request = (uu___260_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___260_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___261_1525 = fs  in
          {
            beta = (uu___261_1525.beta);
            iota = (uu___261_1525.iota);
            zeta = true;
            weak = (uu___261_1525.weak);
            hnf = (uu___261_1525.hnf);
            primops = (uu___261_1525.primops);
            do_not_unfold_pure_lets = (uu___261_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___261_1525.unfold_until);
            unfold_only = (uu___261_1525.unfold_only);
            unfold_fully = (uu___261_1525.unfold_fully);
            unfold_attr = (uu___261_1525.unfold_attr);
            unfold_tac = (uu___261_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___261_1525.pure_subterms_within_computations);
            simplify = (uu___261_1525.simplify);
            erase_universes = (uu___261_1525.erase_universes);
            allow_unbound_universes = (uu___261_1525.allow_unbound_universes);
            reify_ = (uu___261_1525.reify_);
            compress_uvars = (uu___261_1525.compress_uvars);
            no_full_norm = (uu___261_1525.no_full_norm);
            check_no_uvars = (uu___261_1525.check_no_uvars);
            unmeta = (uu___261_1525.unmeta);
            unascribe = (uu___261_1525.unascribe);
            in_full_norm_request = (uu___261_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___261_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___262_1526 = fs  in
          {
            beta = false;
            iota = (uu___262_1526.iota);
            zeta = (uu___262_1526.zeta);
            weak = (uu___262_1526.weak);
            hnf = (uu___262_1526.hnf);
            primops = (uu___262_1526.primops);
            do_not_unfold_pure_lets = (uu___262_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___262_1526.unfold_until);
            unfold_only = (uu___262_1526.unfold_only);
            unfold_fully = (uu___262_1526.unfold_fully);
            unfold_attr = (uu___262_1526.unfold_attr);
            unfold_tac = (uu___262_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___262_1526.pure_subterms_within_computations);
            simplify = (uu___262_1526.simplify);
            erase_universes = (uu___262_1526.erase_universes);
            allow_unbound_universes = (uu___262_1526.allow_unbound_universes);
            reify_ = (uu___262_1526.reify_);
            compress_uvars = (uu___262_1526.compress_uvars);
            no_full_norm = (uu___262_1526.no_full_norm);
            check_no_uvars = (uu___262_1526.check_no_uvars);
            unmeta = (uu___262_1526.unmeta);
            unascribe = (uu___262_1526.unascribe);
            in_full_norm_request = (uu___262_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___262_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___263_1527 = fs  in
          {
            beta = (uu___263_1527.beta);
            iota = false;
            zeta = (uu___263_1527.zeta);
            weak = (uu___263_1527.weak);
            hnf = (uu___263_1527.hnf);
            primops = (uu___263_1527.primops);
            do_not_unfold_pure_lets = (uu___263_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___263_1527.unfold_until);
            unfold_only = (uu___263_1527.unfold_only);
            unfold_fully = (uu___263_1527.unfold_fully);
            unfold_attr = (uu___263_1527.unfold_attr);
            unfold_tac = (uu___263_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___263_1527.pure_subterms_within_computations);
            simplify = (uu___263_1527.simplify);
            erase_universes = (uu___263_1527.erase_universes);
            allow_unbound_universes = (uu___263_1527.allow_unbound_universes);
            reify_ = (uu___263_1527.reify_);
            compress_uvars = (uu___263_1527.compress_uvars);
            no_full_norm = (uu___263_1527.no_full_norm);
            check_no_uvars = (uu___263_1527.check_no_uvars);
            unmeta = (uu___263_1527.unmeta);
            unascribe = (uu___263_1527.unascribe);
            in_full_norm_request = (uu___263_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___263_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___264_1528 = fs  in
          {
            beta = (uu___264_1528.beta);
            iota = (uu___264_1528.iota);
            zeta = false;
            weak = (uu___264_1528.weak);
            hnf = (uu___264_1528.hnf);
            primops = (uu___264_1528.primops);
            do_not_unfold_pure_lets = (uu___264_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___264_1528.unfold_until);
            unfold_only = (uu___264_1528.unfold_only);
            unfold_fully = (uu___264_1528.unfold_fully);
            unfold_attr = (uu___264_1528.unfold_attr);
            unfold_tac = (uu___264_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___264_1528.pure_subterms_within_computations);
            simplify = (uu___264_1528.simplify);
            erase_universes = (uu___264_1528.erase_universes);
            allow_unbound_universes = (uu___264_1528.allow_unbound_universes);
            reify_ = (uu___264_1528.reify_);
            compress_uvars = (uu___264_1528.compress_uvars);
            no_full_norm = (uu___264_1528.no_full_norm);
            check_no_uvars = (uu___264_1528.check_no_uvars);
            unmeta = (uu___264_1528.unmeta);
            unascribe = (uu___264_1528.unascribe);
            in_full_norm_request = (uu___264_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___264_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___265_1530 = fs  in
          {
            beta = (uu___265_1530.beta);
            iota = (uu___265_1530.iota);
            zeta = (uu___265_1530.zeta);
            weak = true;
            hnf = (uu___265_1530.hnf);
            primops = (uu___265_1530.primops);
            do_not_unfold_pure_lets = (uu___265_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___265_1530.unfold_until);
            unfold_only = (uu___265_1530.unfold_only);
            unfold_fully = (uu___265_1530.unfold_fully);
            unfold_attr = (uu___265_1530.unfold_attr);
            unfold_tac = (uu___265_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_1530.pure_subterms_within_computations);
            simplify = (uu___265_1530.simplify);
            erase_universes = (uu___265_1530.erase_universes);
            allow_unbound_universes = (uu___265_1530.allow_unbound_universes);
            reify_ = (uu___265_1530.reify_);
            compress_uvars = (uu___265_1530.compress_uvars);
            no_full_norm = (uu___265_1530.no_full_norm);
            check_no_uvars = (uu___265_1530.check_no_uvars);
            unmeta = (uu___265_1530.unmeta);
            unascribe = (uu___265_1530.unascribe);
            in_full_norm_request = (uu___265_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___266_1531 = fs  in
          {
            beta = (uu___266_1531.beta);
            iota = (uu___266_1531.iota);
            zeta = (uu___266_1531.zeta);
            weak = (uu___266_1531.weak);
            hnf = true;
            primops = (uu___266_1531.primops);
            do_not_unfold_pure_lets = (uu___266_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___266_1531.unfold_until);
            unfold_only = (uu___266_1531.unfold_only);
            unfold_fully = (uu___266_1531.unfold_fully);
            unfold_attr = (uu___266_1531.unfold_attr);
            unfold_tac = (uu___266_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___266_1531.pure_subterms_within_computations);
            simplify = (uu___266_1531.simplify);
            erase_universes = (uu___266_1531.erase_universes);
            allow_unbound_universes = (uu___266_1531.allow_unbound_universes);
            reify_ = (uu___266_1531.reify_);
            compress_uvars = (uu___266_1531.compress_uvars);
            no_full_norm = (uu___266_1531.no_full_norm);
            check_no_uvars = (uu___266_1531.check_no_uvars);
            unmeta = (uu___266_1531.unmeta);
            unascribe = (uu___266_1531.unascribe);
            in_full_norm_request = (uu___266_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___266_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___267_1532 = fs  in
          {
            beta = (uu___267_1532.beta);
            iota = (uu___267_1532.iota);
            zeta = (uu___267_1532.zeta);
            weak = (uu___267_1532.weak);
            hnf = (uu___267_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___267_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___267_1532.unfold_until);
            unfold_only = (uu___267_1532.unfold_only);
            unfold_fully = (uu___267_1532.unfold_fully);
            unfold_attr = (uu___267_1532.unfold_attr);
            unfold_tac = (uu___267_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___267_1532.pure_subterms_within_computations);
            simplify = (uu___267_1532.simplify);
            erase_universes = (uu___267_1532.erase_universes);
            allow_unbound_universes = (uu___267_1532.allow_unbound_universes);
            reify_ = (uu___267_1532.reify_);
            compress_uvars = (uu___267_1532.compress_uvars);
            no_full_norm = (uu___267_1532.no_full_norm);
            check_no_uvars = (uu___267_1532.check_no_uvars);
            unmeta = (uu___267_1532.unmeta);
            unascribe = (uu___267_1532.unascribe);
            in_full_norm_request = (uu___267_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___267_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___268_1533 = fs  in
          {
            beta = (uu___268_1533.beta);
            iota = (uu___268_1533.iota);
            zeta = (uu___268_1533.zeta);
            weak = (uu___268_1533.weak);
            hnf = (uu___268_1533.hnf);
            primops = (uu___268_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___268_1533.unfold_until);
            unfold_only = (uu___268_1533.unfold_only);
            unfold_fully = (uu___268_1533.unfold_fully);
            unfold_attr = (uu___268_1533.unfold_attr);
            unfold_tac = (uu___268_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___268_1533.pure_subterms_within_computations);
            simplify = (uu___268_1533.simplify);
            erase_universes = (uu___268_1533.erase_universes);
            allow_unbound_universes = (uu___268_1533.allow_unbound_universes);
            reify_ = (uu___268_1533.reify_);
            compress_uvars = (uu___268_1533.compress_uvars);
            no_full_norm = (uu___268_1533.no_full_norm);
            check_no_uvars = (uu___268_1533.check_no_uvars);
            unmeta = (uu___268_1533.unmeta);
            unascribe = (uu___268_1533.unascribe);
            in_full_norm_request = (uu___268_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___268_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___269_1535 = fs  in
          {
            beta = (uu___269_1535.beta);
            iota = (uu___269_1535.iota);
            zeta = (uu___269_1535.zeta);
            weak = (uu___269_1535.weak);
            hnf = (uu___269_1535.hnf);
            primops = (uu___269_1535.primops);
            do_not_unfold_pure_lets = (uu___269_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___269_1535.unfold_only);
            unfold_fully = (uu___269_1535.unfold_fully);
            unfold_attr = (uu___269_1535.unfold_attr);
            unfold_tac = (uu___269_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___269_1535.pure_subterms_within_computations);
            simplify = (uu___269_1535.simplify);
            erase_universes = (uu___269_1535.erase_universes);
            allow_unbound_universes = (uu___269_1535.allow_unbound_universes);
            reify_ = (uu___269_1535.reify_);
            compress_uvars = (uu___269_1535.compress_uvars);
            no_full_norm = (uu___269_1535.no_full_norm);
            check_no_uvars = (uu___269_1535.check_no_uvars);
            unmeta = (uu___269_1535.unmeta);
            unascribe = (uu___269_1535.unascribe);
            in_full_norm_request = (uu___269_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___269_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___270_1539 = fs  in
          {
            beta = (uu___270_1539.beta);
            iota = (uu___270_1539.iota);
            zeta = (uu___270_1539.zeta);
            weak = (uu___270_1539.weak);
            hnf = (uu___270_1539.hnf);
            primops = (uu___270_1539.primops);
            do_not_unfold_pure_lets = (uu___270_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___270_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___270_1539.unfold_fully);
            unfold_attr = (uu___270_1539.unfold_attr);
            unfold_tac = (uu___270_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___270_1539.pure_subterms_within_computations);
            simplify = (uu___270_1539.simplify);
            erase_universes = (uu___270_1539.erase_universes);
            allow_unbound_universes = (uu___270_1539.allow_unbound_universes);
            reify_ = (uu___270_1539.reify_);
            compress_uvars = (uu___270_1539.compress_uvars);
            no_full_norm = (uu___270_1539.no_full_norm);
            check_no_uvars = (uu___270_1539.check_no_uvars);
            unmeta = (uu___270_1539.unmeta);
            unascribe = (uu___270_1539.unascribe);
            in_full_norm_request = (uu___270_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___270_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___271_1545 = fs  in
          {
            beta = (uu___271_1545.beta);
            iota = (uu___271_1545.iota);
            zeta = (uu___271_1545.zeta);
            weak = (uu___271_1545.weak);
            hnf = (uu___271_1545.hnf);
            primops = (uu___271_1545.primops);
            do_not_unfold_pure_lets = (uu___271_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___271_1545.unfold_until);
            unfold_only = (uu___271_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___271_1545.unfold_attr);
            unfold_tac = (uu___271_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___271_1545.pure_subterms_within_computations);
            simplify = (uu___271_1545.simplify);
            erase_universes = (uu___271_1545.erase_universes);
            allow_unbound_universes = (uu___271_1545.allow_unbound_universes);
            reify_ = (uu___271_1545.reify_);
            compress_uvars = (uu___271_1545.compress_uvars);
            no_full_norm = (uu___271_1545.no_full_norm);
            check_no_uvars = (uu___271_1545.check_no_uvars);
            unmeta = (uu___271_1545.unmeta);
            unascribe = (uu___271_1545.unascribe);
            in_full_norm_request = (uu___271_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___271_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___272_1549 = fs  in
          {
            beta = (uu___272_1549.beta);
            iota = (uu___272_1549.iota);
            zeta = (uu___272_1549.zeta);
            weak = (uu___272_1549.weak);
            hnf = (uu___272_1549.hnf);
            primops = (uu___272_1549.primops);
            do_not_unfold_pure_lets = (uu___272_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___272_1549.unfold_until);
            unfold_only = (uu___272_1549.unfold_only);
            unfold_fully = (uu___272_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___272_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___272_1549.pure_subterms_within_computations);
            simplify = (uu___272_1549.simplify);
            erase_universes = (uu___272_1549.erase_universes);
            allow_unbound_universes = (uu___272_1549.allow_unbound_universes);
            reify_ = (uu___272_1549.reify_);
            compress_uvars = (uu___272_1549.compress_uvars);
            no_full_norm = (uu___272_1549.no_full_norm);
            check_no_uvars = (uu___272_1549.check_no_uvars);
            unmeta = (uu___272_1549.unmeta);
            unascribe = (uu___272_1549.unascribe);
            in_full_norm_request = (uu___272_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___272_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___273_1550 = fs  in
          {
            beta = (uu___273_1550.beta);
            iota = (uu___273_1550.iota);
            zeta = (uu___273_1550.zeta);
            weak = (uu___273_1550.weak);
            hnf = (uu___273_1550.hnf);
            primops = (uu___273_1550.primops);
            do_not_unfold_pure_lets = (uu___273_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___273_1550.unfold_until);
            unfold_only = (uu___273_1550.unfold_only);
            unfold_fully = (uu___273_1550.unfold_fully);
            unfold_attr = (uu___273_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___273_1550.pure_subterms_within_computations);
            simplify = (uu___273_1550.simplify);
            erase_universes = (uu___273_1550.erase_universes);
            allow_unbound_universes = (uu___273_1550.allow_unbound_universes);
            reify_ = (uu___273_1550.reify_);
            compress_uvars = (uu___273_1550.compress_uvars);
            no_full_norm = (uu___273_1550.no_full_norm);
            check_no_uvars = (uu___273_1550.check_no_uvars);
            unmeta = (uu___273_1550.unmeta);
            unascribe = (uu___273_1550.unascribe);
            in_full_norm_request = (uu___273_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___273_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___274_1551 = fs  in
          {
            beta = (uu___274_1551.beta);
            iota = (uu___274_1551.iota);
            zeta = (uu___274_1551.zeta);
            weak = (uu___274_1551.weak);
            hnf = (uu___274_1551.hnf);
            primops = (uu___274_1551.primops);
            do_not_unfold_pure_lets = (uu___274_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___274_1551.unfold_until);
            unfold_only = (uu___274_1551.unfold_only);
            unfold_fully = (uu___274_1551.unfold_fully);
            unfold_attr = (uu___274_1551.unfold_attr);
            unfold_tac = (uu___274_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___274_1551.simplify);
            erase_universes = (uu___274_1551.erase_universes);
            allow_unbound_universes = (uu___274_1551.allow_unbound_universes);
            reify_ = (uu___274_1551.reify_);
            compress_uvars = (uu___274_1551.compress_uvars);
            no_full_norm = (uu___274_1551.no_full_norm);
            check_no_uvars = (uu___274_1551.check_no_uvars);
            unmeta = (uu___274_1551.unmeta);
            unascribe = (uu___274_1551.unascribe);
            in_full_norm_request = (uu___274_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___274_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___275_1552 = fs  in
          {
            beta = (uu___275_1552.beta);
            iota = (uu___275_1552.iota);
            zeta = (uu___275_1552.zeta);
            weak = (uu___275_1552.weak);
            hnf = (uu___275_1552.hnf);
            primops = (uu___275_1552.primops);
            do_not_unfold_pure_lets = (uu___275_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___275_1552.unfold_until);
            unfold_only = (uu___275_1552.unfold_only);
            unfold_fully = (uu___275_1552.unfold_fully);
            unfold_attr = (uu___275_1552.unfold_attr);
            unfold_tac = (uu___275_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___275_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___275_1552.erase_universes);
            allow_unbound_universes = (uu___275_1552.allow_unbound_universes);
            reify_ = (uu___275_1552.reify_);
            compress_uvars = (uu___275_1552.compress_uvars);
            no_full_norm = (uu___275_1552.no_full_norm);
            check_no_uvars = (uu___275_1552.check_no_uvars);
            unmeta = (uu___275_1552.unmeta);
            unascribe = (uu___275_1552.unascribe);
            in_full_norm_request = (uu___275_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___275_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___276_1553 = fs  in
          {
            beta = (uu___276_1553.beta);
            iota = (uu___276_1553.iota);
            zeta = (uu___276_1553.zeta);
            weak = (uu___276_1553.weak);
            hnf = (uu___276_1553.hnf);
            primops = (uu___276_1553.primops);
            do_not_unfold_pure_lets = (uu___276_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___276_1553.unfold_until);
            unfold_only = (uu___276_1553.unfold_only);
            unfold_fully = (uu___276_1553.unfold_fully);
            unfold_attr = (uu___276_1553.unfold_attr);
            unfold_tac = (uu___276_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___276_1553.pure_subterms_within_computations);
            simplify = (uu___276_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___276_1553.allow_unbound_universes);
            reify_ = (uu___276_1553.reify_);
            compress_uvars = (uu___276_1553.compress_uvars);
            no_full_norm = (uu___276_1553.no_full_norm);
            check_no_uvars = (uu___276_1553.check_no_uvars);
            unmeta = (uu___276_1553.unmeta);
            unascribe = (uu___276_1553.unascribe);
            in_full_norm_request = (uu___276_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___276_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___277_1554 = fs  in
          {
            beta = (uu___277_1554.beta);
            iota = (uu___277_1554.iota);
            zeta = (uu___277_1554.zeta);
            weak = (uu___277_1554.weak);
            hnf = (uu___277_1554.hnf);
            primops = (uu___277_1554.primops);
            do_not_unfold_pure_lets = (uu___277_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___277_1554.unfold_until);
            unfold_only = (uu___277_1554.unfold_only);
            unfold_fully = (uu___277_1554.unfold_fully);
            unfold_attr = (uu___277_1554.unfold_attr);
            unfold_tac = (uu___277_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___277_1554.pure_subterms_within_computations);
            simplify = (uu___277_1554.simplify);
            erase_universes = (uu___277_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___277_1554.reify_);
            compress_uvars = (uu___277_1554.compress_uvars);
            no_full_norm = (uu___277_1554.no_full_norm);
            check_no_uvars = (uu___277_1554.check_no_uvars);
            unmeta = (uu___277_1554.unmeta);
            unascribe = (uu___277_1554.unascribe);
            in_full_norm_request = (uu___277_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___277_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___278_1555 = fs  in
          {
            beta = (uu___278_1555.beta);
            iota = (uu___278_1555.iota);
            zeta = (uu___278_1555.zeta);
            weak = (uu___278_1555.weak);
            hnf = (uu___278_1555.hnf);
            primops = (uu___278_1555.primops);
            do_not_unfold_pure_lets = (uu___278_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___278_1555.unfold_until);
            unfold_only = (uu___278_1555.unfold_only);
            unfold_fully = (uu___278_1555.unfold_fully);
            unfold_attr = (uu___278_1555.unfold_attr);
            unfold_tac = (uu___278_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___278_1555.pure_subterms_within_computations);
            simplify = (uu___278_1555.simplify);
            erase_universes = (uu___278_1555.erase_universes);
            allow_unbound_universes = (uu___278_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___278_1555.compress_uvars);
            no_full_norm = (uu___278_1555.no_full_norm);
            check_no_uvars = (uu___278_1555.check_no_uvars);
            unmeta = (uu___278_1555.unmeta);
            unascribe = (uu___278_1555.unascribe);
            in_full_norm_request = (uu___278_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___278_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___279_1556 = fs  in
          {
            beta = (uu___279_1556.beta);
            iota = (uu___279_1556.iota);
            zeta = (uu___279_1556.zeta);
            weak = (uu___279_1556.weak);
            hnf = (uu___279_1556.hnf);
            primops = (uu___279_1556.primops);
            do_not_unfold_pure_lets = (uu___279_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___279_1556.unfold_until);
            unfold_only = (uu___279_1556.unfold_only);
            unfold_fully = (uu___279_1556.unfold_fully);
            unfold_attr = (uu___279_1556.unfold_attr);
            unfold_tac = (uu___279_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___279_1556.pure_subterms_within_computations);
            simplify = (uu___279_1556.simplify);
            erase_universes = (uu___279_1556.erase_universes);
            allow_unbound_universes = (uu___279_1556.allow_unbound_universes);
            reify_ = (uu___279_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___279_1556.no_full_norm);
            check_no_uvars = (uu___279_1556.check_no_uvars);
            unmeta = (uu___279_1556.unmeta);
            unascribe = (uu___279_1556.unascribe);
            in_full_norm_request = (uu___279_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___279_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___280_1557 = fs  in
          {
            beta = (uu___280_1557.beta);
            iota = (uu___280_1557.iota);
            zeta = (uu___280_1557.zeta);
            weak = (uu___280_1557.weak);
            hnf = (uu___280_1557.hnf);
            primops = (uu___280_1557.primops);
            do_not_unfold_pure_lets = (uu___280_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___280_1557.unfold_until);
            unfold_only = (uu___280_1557.unfold_only);
            unfold_fully = (uu___280_1557.unfold_fully);
            unfold_attr = (uu___280_1557.unfold_attr);
            unfold_tac = (uu___280_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___280_1557.pure_subterms_within_computations);
            simplify = (uu___280_1557.simplify);
            erase_universes = (uu___280_1557.erase_universes);
            allow_unbound_universes = (uu___280_1557.allow_unbound_universes);
            reify_ = (uu___280_1557.reify_);
            compress_uvars = (uu___280_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___280_1557.check_no_uvars);
            unmeta = (uu___280_1557.unmeta);
            unascribe = (uu___280_1557.unascribe);
            in_full_norm_request = (uu___280_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___280_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___281_1558 = fs  in
          {
            beta = (uu___281_1558.beta);
            iota = (uu___281_1558.iota);
            zeta = (uu___281_1558.zeta);
            weak = (uu___281_1558.weak);
            hnf = (uu___281_1558.hnf);
            primops = (uu___281_1558.primops);
            do_not_unfold_pure_lets = (uu___281_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___281_1558.unfold_until);
            unfold_only = (uu___281_1558.unfold_only);
            unfold_fully = (uu___281_1558.unfold_fully);
            unfold_attr = (uu___281_1558.unfold_attr);
            unfold_tac = (uu___281_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___281_1558.pure_subterms_within_computations);
            simplify = (uu___281_1558.simplify);
            erase_universes = (uu___281_1558.erase_universes);
            allow_unbound_universes = (uu___281_1558.allow_unbound_universes);
            reify_ = (uu___281_1558.reify_);
            compress_uvars = (uu___281_1558.compress_uvars);
            no_full_norm = (uu___281_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___281_1558.unmeta);
            unascribe = (uu___281_1558.unascribe);
            in_full_norm_request = (uu___281_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___281_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___282_1559 = fs  in
          {
            beta = (uu___282_1559.beta);
            iota = (uu___282_1559.iota);
            zeta = (uu___282_1559.zeta);
            weak = (uu___282_1559.weak);
            hnf = (uu___282_1559.hnf);
            primops = (uu___282_1559.primops);
            do_not_unfold_pure_lets = (uu___282_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___282_1559.unfold_until);
            unfold_only = (uu___282_1559.unfold_only);
            unfold_fully = (uu___282_1559.unfold_fully);
            unfold_attr = (uu___282_1559.unfold_attr);
            unfold_tac = (uu___282_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___282_1559.pure_subterms_within_computations);
            simplify = (uu___282_1559.simplify);
            erase_universes = (uu___282_1559.erase_universes);
            allow_unbound_universes = (uu___282_1559.allow_unbound_universes);
            reify_ = (uu___282_1559.reify_);
            compress_uvars = (uu___282_1559.compress_uvars);
            no_full_norm = (uu___282_1559.no_full_norm);
            check_no_uvars = (uu___282_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___282_1559.unascribe);
            in_full_norm_request = (uu___282_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___282_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___283_1560 = fs  in
          {
            beta = (uu___283_1560.beta);
            iota = (uu___283_1560.iota);
            zeta = (uu___283_1560.zeta);
            weak = (uu___283_1560.weak);
            hnf = (uu___283_1560.hnf);
            primops = (uu___283_1560.primops);
            do_not_unfold_pure_lets = (uu___283_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___283_1560.unfold_until);
            unfold_only = (uu___283_1560.unfold_only);
            unfold_fully = (uu___283_1560.unfold_fully);
            unfold_attr = (uu___283_1560.unfold_attr);
            unfold_tac = (uu___283_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___283_1560.pure_subterms_within_computations);
            simplify = (uu___283_1560.simplify);
            erase_universes = (uu___283_1560.erase_universes);
            allow_unbound_universes = (uu___283_1560.allow_unbound_universes);
            reify_ = (uu___283_1560.reify_);
            compress_uvars = (uu___283_1560.compress_uvars);
            no_full_norm = (uu___283_1560.no_full_norm);
            check_no_uvars = (uu___283_1560.check_no_uvars);
            unmeta = (uu___283_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___283_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___283_1560.weakly_reduce_scrutinee)
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
  fun uu___241_3245  ->
    match uu___241_3245 with
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
  fun uu___242_3307  ->
    match uu___242_3307 with
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
  fun uu___243_3443  ->
    match uu___243_3443 with | [] -> true | uu____3446 -> false
  
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
                    let uu____3961 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3961
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3962 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3963 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3964 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3965 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3989 ->
                           let uu____4002 =
                             let uu____4003 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4004 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4003 uu____4004
                              in
                           failwith uu____4002
                       | uu____4007 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___244_4042  ->
                                         match uu___244_4042 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4049 =
                                               let uu____4056 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4056)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4049
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___288_4066 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___288_4066.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___288_4066.FStar_Syntax_Syntax.sort)
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
                                              | uu____4071 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4074 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___289_4078 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___289_4078.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___289_4078.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4099 =
                        let uu____4100 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4100  in
                      mk uu____4099 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4108 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4108  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4110 = lookup_bvar env x  in
                    (match uu____4110 with
                     | Univ uu____4113 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___290_4117 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___290_4117.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___290_4117.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4123,uu____4124) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4209  ->
                              fun stack1  ->
                                match uu____4209 with
                                | (a,aq) ->
                                    let uu____4221 =
                                      let uu____4222 =
                                        let uu____4229 =
                                          let uu____4230 =
                                            let uu____4261 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4261, false)  in
                                          Clos uu____4230  in
                                        (uu____4229, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4222  in
                                    uu____4221 :: stack1) args)
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
                    let uu____4437 = close_binders cfg env bs  in
                    (match uu____4437 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4484 =
                      let uu____4495 =
                        let uu____4502 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4502]  in
                      close_binders cfg env uu____4495  in
                    (match uu____4484 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4537 =
                             let uu____4538 =
                               let uu____4545 =
                                 let uu____4546 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4546
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4545, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4538  in
                           mk uu____4537 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4637 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4637
                      | FStar_Util.Inr c ->
                          let uu____4651 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4651
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4670 =
                        let uu____4671 =
                          let uu____4698 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4698, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4671  in
                      mk uu____4670 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4744 =
                            let uu____4745 =
                              let uu____4752 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4752, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4745  in
                          mk uu____4744 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4804  -> dummy :: env1) env
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
                    let uu____4825 =
                      let uu____4836 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4836
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4855 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___291_4871 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___291_4871.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___291_4871.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4855))
                       in
                    (match uu____4825 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___292_4889 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___292_4889.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___292_4889.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___292_4889.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___292_4889.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4903,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4966  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4983 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4983
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4995  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5019 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5019
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___293_5027 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___293_5027.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___293_5027.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___294_5028 = lb  in
                      let uu____5029 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___294_5028.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___294_5028.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5029;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___294_5028.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___294_5028.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5061  -> fun env1  -> dummy :: env1)
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
            (fun uu____5150  ->
               let uu____5151 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5152 = env_to_string env  in
               let uu____5153 = stack_to_string stack  in
               let uu____5154 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5151 uu____5152 uu____5153 uu____5154);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5159,uu____5160),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5237 = close_binders cfg env' bs  in
               (match uu____5237 with
                | (bs1,uu____5251) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5267 =
                      let uu___295_5270 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___295_5270.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___295_5270.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5267)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5326 =
                 match uu____5326 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5441 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5470 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5554  ->
                                     fun uu____5555  ->
                                       match (uu____5554, uu____5555) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5694 = norm_pat env4 p1
                                              in
                                           (match uu____5694 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5470 with
                            | (pats1,env4) ->
                                ((let uu___296_5856 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___296_5856.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___297_5875 = x  in
                             let uu____5876 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___297_5875.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___297_5875.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5876
                             }  in
                           ((let uu___298_5890 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___298_5890.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___299_5901 = x  in
                             let uu____5902 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___299_5901.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___299_5901.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5902
                             }  in
                           ((let uu___300_5916 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___300_5916.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___301_5932 = x  in
                             let uu____5933 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___301_5932.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___301_5932.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5933
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___302_5950 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___302_5950.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5955 = norm_pat env2 pat  in
                     (match uu____5955 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6024 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6024
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6043 =
                   let uu____6044 =
                     let uu____6067 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6067)  in
                   FStar_Syntax_Syntax.Tm_match uu____6044  in
                 mk uu____6043 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6180 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6269  ->
                                       match uu____6269 with
                                       | (a,q) ->
                                           let uu____6288 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6288, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6180
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6299 =
                       let uu____6306 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6306)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6299
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6318 =
                       let uu____6327 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6327)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6318
                 | uu____6332 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6338 -> failwith "Impossible: unexpected stack element")

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
        let uu____6352 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6425  ->
                  fun uu____6426  ->
                    match (uu____6425, uu____6426) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___303_6544 = b  in
                          let uu____6545 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___303_6544.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___303_6544.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6545
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6352 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6662 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6675 = inline_closure_env cfg env [] t  in
                 let uu____6676 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6675 uu____6676
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6689 = inline_closure_env cfg env [] t  in
                 let uu____6690 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6689 uu____6690
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6734  ->
                           match uu____6734 with
                           | (a,q) ->
                               let uu____6747 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6747, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___245_6762  ->
                           match uu___245_6762 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6766 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6766
                           | f -> f))
                    in
                 let uu____6770 =
                   let uu___304_6771 = c1  in
                   let uu____6772 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6772;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___304_6771.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6770)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___246_6782  ->
            match uu___246_6782 with
            | FStar_Syntax_Syntax.DECREASES uu____6783 -> false
            | uu____6786 -> true))

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
                   (fun uu___247_6804  ->
                      match uu___247_6804 with
                      | FStar_Syntax_Syntax.DECREASES uu____6805 -> false
                      | uu____6808 -> true))
               in
            let rc1 =
              let uu___305_6810 = rc  in
              let uu____6811 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___305_6810.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6811;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6820 -> lopt

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
    let uu____6925 =
      let uu____6934 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6934  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6925  in
  let arg_as_bounded_int uu____6960 =
    match uu____6960 with
    | (a,uu____6972) ->
        let uu____6979 =
          let uu____6980 = FStar_Syntax_Subst.compress a  in
          uu____6980.FStar_Syntax_Syntax.n  in
        (match uu____6979 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6990;
                FStar_Syntax_Syntax.vars = uu____6991;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6993;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6994;_},uu____6995)::[])
             when
             let uu____7034 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7034 "int_to_t" ->
             let uu____7035 =
               let uu____7040 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7040)  in
             FStar_Pervasives_Native.Some uu____7035
         | uu____7045 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7093 = f a  in FStar_Pervasives_Native.Some uu____7093
    | uu____7094 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7150 = f a0 a1  in FStar_Pervasives_Native.Some uu____7150
    | uu____7151 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7209 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7209  in
  let binary_op as_a f res args =
    let uu____7280 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7280  in
  let as_primitive_step is_strong uu____7317 =
    match uu____7317 with
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
           let uu____7377 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7377)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7413 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7413)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7442 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7442)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7478 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7478)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7514 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7514)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7646 =
          let uu____7655 = as_a a  in
          let uu____7658 = as_b b  in (uu____7655, uu____7658)  in
        (match uu____7646 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7673 =
               let uu____7674 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7674  in
             FStar_Pervasives_Native.Some uu____7673
         | uu____7675 -> FStar_Pervasives_Native.None)
    | uu____7684 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7704 =
        let uu____7705 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7705  in
      mk uu____7704 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7719 =
      let uu____7722 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7722  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7719  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7764 =
      let uu____7765 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7765  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7764
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7829 = arg_as_string a1  in
        (match uu____7829 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7835 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7835 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7848 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7848
              | uu____7849 -> FStar_Pervasives_Native.None)
         | uu____7854 -> FStar_Pervasives_Native.None)
    | uu____7857 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7877 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7877
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7914 =
          let uu____7935 = arg_as_string fn  in
          let uu____7938 = arg_as_int from_line  in
          let uu____7941 = arg_as_int from_col  in
          let uu____7944 = arg_as_int to_line  in
          let uu____7947 = arg_as_int to_col  in
          (uu____7935, uu____7938, uu____7941, uu____7944, uu____7947)  in
        (match uu____7914 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7978 =
                 let uu____7979 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7980 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7979 uu____7980  in
               let uu____7981 =
                 let uu____7982 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7983 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7982 uu____7983  in
               FStar_Range.mk_range fn1 uu____7978 uu____7981  in
             let uu____7984 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7984
         | uu____7985 -> FStar_Pervasives_Native.None)
    | uu____8006 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8039)::(a1,uu____8041)::(a2,uu____8043)::[] ->
        let uu____8080 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8080 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8085 -> FStar_Pervasives_Native.None)
    | uu____8086 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8117)::[] ->
        let uu____8126 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8126 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8132 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8132
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8133 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8159 =
      let uu____8176 =
        let uu____8193 =
          let uu____8210 =
            let uu____8227 =
              let uu____8244 =
                let uu____8261 =
                  let uu____8278 =
                    let uu____8295 =
                      let uu____8312 =
                        let uu____8329 =
                          let uu____8346 =
                            let uu____8363 =
                              let uu____8380 =
                                let uu____8397 =
                                  let uu____8414 =
                                    let uu____8431 =
                                      let uu____8448 =
                                        let uu____8465 =
                                          let uu____8482 =
                                            let uu____8499 =
                                              let uu____8516 =
                                                let uu____8531 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8531,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8540 =
                                                let uu____8557 =
                                                  let uu____8572 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8572,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8585 =
                                                  let uu____8602 =
                                                    let uu____8617 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8617,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8626 =
                                                    let uu____8643 =
                                                      let uu____8658 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8658,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8643]  in
                                                  uu____8602 :: uu____8626
                                                   in
                                                uu____8557 :: uu____8585  in
                                              uu____8516 :: uu____8540  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8499
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8482
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8465
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8448
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8431
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8878 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8878 y)))
                                    :: uu____8414
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8397
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8380
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8363
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8346
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8329
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8312
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9073 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9073)))
                      :: uu____8295
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9103 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9103)))
                    :: uu____8278
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9133 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9133)))
                  :: uu____8261
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9163 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9163)))
                :: uu____8244
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8227
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8210
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8193
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8176
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8159
     in
  let weak_ops =
    let uu____9318 =
      let uu____9333 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9333, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9318]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9413 =
        let uu____9418 =
          let uu____9419 = FStar_Syntax_Syntax.as_arg c  in [uu____9419]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9418  in
      uu____9413 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9493 =
                let uu____9508 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9508, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9530  ->
                          fun uu____9531  ->
                            match (uu____9530, uu____9531) with
                            | ((int_to_t1,x),(uu____9550,y)) ->
                                let uu____9560 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9560)))
                 in
              let uu____9561 =
                let uu____9578 =
                  let uu____9593 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9593, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9615  ->
                            fun uu____9616  ->
                              match (uu____9615, uu____9616) with
                              | ((int_to_t1,x),(uu____9635,y)) ->
                                  let uu____9645 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9645)))
                   in
                let uu____9646 =
                  let uu____9663 =
                    let uu____9678 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9678, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9700  ->
                              fun uu____9701  ->
                                match (uu____9700, uu____9701) with
                                | ((int_to_t1,x),(uu____9720,y)) ->
                                    let uu____9730 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9730)))
                     in
                  let uu____9731 =
                    let uu____9748 =
                      let uu____9763 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9763, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9781  ->
                                match uu____9781 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9748]  in
                  uu____9663 :: uu____9731  in
                uu____9578 :: uu____9646  in
              uu____9493 :: uu____9561))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9911 =
                let uu____9926 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9926, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9948  ->
                          fun uu____9949  ->
                            match (uu____9948, uu____9949) with
                            | ((int_to_t1,x),(uu____9968,y)) ->
                                let uu____9978 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9978)))
                 in
              let uu____9979 =
                let uu____9996 =
                  let uu____10011 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10011, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10033  ->
                            fun uu____10034  ->
                              match (uu____10033, uu____10034) with
                              | ((int_to_t1,x),(uu____10053,y)) ->
                                  let uu____10063 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10063)))
                   in
                [uu____9996]  in
              uu____9911 :: uu____9979))
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
    | (_typ,uu____10193)::(a1,uu____10195)::(a2,uu____10197)::[] ->
        let uu____10234 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10234 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10238 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10238.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10238.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___307_10240 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___307_10240.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___307_10240.FStar_Syntax_Syntax.vars)
                })
         | uu____10241 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10243)::uu____10244::(a1,uu____10246)::(a2,uu____10248)::[]
        ->
        let uu____10297 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10297 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10301 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10301.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10301.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___307_10303 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___307_10303.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___307_10303.FStar_Syntax_Syntax.vars)
                })
         | uu____10304 -> FStar_Pervasives_Native.None)
    | uu____10305 -> failwith "Unexpected number of arguments"  in
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
    let uu____10359 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10359 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10411 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10411) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10473  ->
           fun subst1  ->
             match uu____10473 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10514,uu____10515)) ->
                      let uu____10574 = b  in
                      (match uu____10574 with
                       | (bv,uu____10582) ->
                           let uu____10583 =
                             let uu____10584 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10584  in
                           if uu____10583
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10589 = unembed_binder term1  in
                              match uu____10589 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10596 =
                                      let uu___308_10597 = bv  in
                                      let uu____10598 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___308_10597.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___308_10597.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10598
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10596
                                     in
                                  let b_for_x =
                                    let uu____10602 =
                                      let uu____10609 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10609)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10602  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___248_10623  ->
                                         match uu___248_10623 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10624,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10626;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10627;_})
                                             ->
                                             let uu____10632 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10632
                                         | uu____10633 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10634 -> subst1)) env []
  
let reduce_primops :
  'Auu____10657 'Auu____10658 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10657) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10658 ->
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
            (let uu____10706 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10706 with
             | (head1,args) ->
                 let uu____10745 =
                   let uu____10746 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10746.FStar_Syntax_Syntax.n  in
                 (match uu____10745 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10752 = find_prim_step cfg fv  in
                      (match uu____10752 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10778  ->
                                   let uu____10779 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10780 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10787 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10779 uu____10780 uu____10787);
                              tm)
                           else
                             (let uu____10789 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10789 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10902  ->
                                        let uu____10903 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10903);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10906  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10908 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10908 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10916  ->
                                              let uu____10917 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10917);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10923  ->
                                              let uu____10924 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10925 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10924 uu____10925);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10926 ->
                           (log_primops cfg
                              (fun uu____10930  ->
                                 let uu____10931 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10931);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10935  ->
                            let uu____10936 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10936);
                       (match args with
                        | (a1,uu____10940)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10957 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10969  ->
                            let uu____10970 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10970);
                       (match args with
                        | (t,uu____10974)::(r,uu____10976)::[] ->
                            let uu____11003 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11003 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11009 -> tm))
                  | uu____11018 -> tm))
  
let reduce_equality :
  'Auu____11029 'Auu____11030 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11029) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11030 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___309_11076 = cfg  in
         {
           steps =
             (let uu___310_11079 = default_steps  in
              {
                beta = (uu___310_11079.beta);
                iota = (uu___310_11079.iota);
                zeta = (uu___310_11079.zeta);
                weak = (uu___310_11079.weak);
                hnf = (uu___310_11079.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___310_11079.do_not_unfold_pure_lets);
                unfold_until = (uu___310_11079.unfold_until);
                unfold_only = (uu___310_11079.unfold_only);
                unfold_fully = (uu___310_11079.unfold_fully);
                unfold_attr = (uu___310_11079.unfold_attr);
                unfold_tac = (uu___310_11079.unfold_tac);
                pure_subterms_within_computations =
                  (uu___310_11079.pure_subterms_within_computations);
                simplify = (uu___310_11079.simplify);
                erase_universes = (uu___310_11079.erase_universes);
                allow_unbound_universes =
                  (uu___310_11079.allow_unbound_universes);
                reify_ = (uu___310_11079.reify_);
                compress_uvars = (uu___310_11079.compress_uvars);
                no_full_norm = (uu___310_11079.no_full_norm);
                check_no_uvars = (uu___310_11079.check_no_uvars);
                unmeta = (uu___310_11079.unmeta);
                unascribe = (uu___310_11079.unascribe);
                in_full_norm_request = (uu___310_11079.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___310_11079.weakly_reduce_scrutinee)
              });
           tcenv = (uu___309_11076.tcenv);
           debug = (uu___309_11076.debug);
           delta_level = (uu___309_11076.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___309_11076.strong);
           memoize_lazy = (uu___309_11076.memoize_lazy);
           normalize_pure_lets = (uu___309_11076.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11086 .
    FStar_Syntax_Syntax.term -> 'Auu____11086 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11101 =
        let uu____11108 =
          let uu____11109 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11109.FStar_Syntax_Syntax.n  in
        (uu____11108, args)  in
      match uu____11101 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11115::uu____11116::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11120::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11125::uu____11126::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11129 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___249_11142  ->
    match uu___249_11142 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11148 =
          let uu____11151 =
            let uu____11152 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11152  in
          [uu____11151]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11148
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11158 =
          let uu____11161 =
            let uu____11162 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11162  in
          [uu____11161]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11158
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11185 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11185)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11236 =
            let uu____11241 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11241 s  in
          match uu____11236 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11257 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11257
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11283::(tm,uu____11285)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11314)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11335)::uu____11336::(tm,uu____11338)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11379 =
              let uu____11384 = full_norm steps  in parse_steps uu____11384
               in
            (match uu____11379 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11423 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___250_11442  ->
    match uu___250_11442 with
    | (App
        (uu____11445,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11446;
                       FStar_Syntax_Syntax.vars = uu____11447;_},uu____11448,uu____11449))::uu____11450
        -> true
    | uu____11455 -> false
  
let firstn :
  'Auu____11464 .
    Prims.int ->
      'Auu____11464 Prims.list ->
        ('Auu____11464 Prims.list,'Auu____11464 Prims.list)
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
          (uu____11506,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11507;
                         FStar_Syntax_Syntax.vars = uu____11508;_},uu____11509,uu____11510))::uu____11511
          -> (cfg.steps).reify_
      | uu____11516 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11539) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11549) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11568  ->
                  match uu____11568 with
                  | (a,uu____11576) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11582 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11605 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11606 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11619 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11620 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11621 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11622 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11623 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11624 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11631 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11638 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11651 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11668 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11681 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11688 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11750  ->
                   match uu____11750 with
                   | (a,uu____11758) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11765) ->
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
                     (fun uu____11887  ->
                        match uu____11887 with
                        | (a,uu____11895) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11900,uu____11901,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11907,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11913 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11920 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11921 -> false))
  
let decide_unfolding :
  'Auu____11936 .
    cfg ->
      'Auu____11936 Prims.list ->
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
                (fun uu____12028  ->
                   let uu____12029 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____12030 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____12031 =
                     let uu____12032 =
                       let uu____12035 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____12035
                        in
                     stack_to_string uu____12032  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____12029 uu____12030 uu____12031);
              (let attrs =
                 let uu____12061 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____12061 with
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
                   (fun uu____12189  ->
                      fun uu____12190  ->
                        match (uu____12189, uu____12190) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____12250 =
                 match uu____12250 with
                 | (x,y,z) ->
                     let uu____12260 = FStar_Util.string_of_bool x  in
                     let uu____12261 = FStar_Util.string_of_bool y  in
                     let uu____12262 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____12260 uu____12261
                       uu____12262
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____12308 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____12354  ->
                           let uu____12355 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____12356 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____12355 uu____12356);
                      if b then reif else no)
                 | uu____12364 when
                     let uu____12405 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____12405 -> no
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____12409),uu____12410);
                        FStar_Syntax_Syntax.sigrng = uu____12411;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____12413;
                        FStar_Syntax_Syntax.sigattrs = uu____12414;_},uu____12415),uu____12416),uu____12417,uu____12418,uu____12419)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     -> no
                 | (uu____12522,uu____12523,uu____12524,uu____12525) when
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
                          ((is_rec,uu____12591),uu____12592);
                        FStar_Syntax_Syntax.sigrng = uu____12593;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____12595;
                        FStar_Syntax_Syntax.sigattrs = uu____12596;_},uu____12597),uu____12598),uu____12599,uu____12600,uu____12601)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     no
                 | (uu____12704,FStar_Pervasives_Native.Some
                    uu____12705,uu____12706,uu____12707) ->
                     (log_unfolding cfg
                        (fun uu____12775  ->
                           let uu____12776 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____12776);
                      (let uu____12777 =
                         let uu____12786 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____12806 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____12806
                            in
                         let uu____12813 =
                           let uu____12822 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____12842 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____12842
                              in
                           let uu____12851 =
                             let uu____12860 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____12880 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____12880
                                in
                             [uu____12860]  in
                           uu____12822 :: uu____12851  in
                         uu____12786 :: uu____12813  in
                       comb_or uu____12777))
                 | (uu____12911,uu____12912,FStar_Pervasives_Native.Some
                    uu____12913,uu____12914) ->
                     (log_unfolding cfg
                        (fun uu____12982  ->
                           let uu____12983 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____12983);
                      (let uu____12984 =
                         let uu____12993 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13013 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13013
                            in
                         let uu____13020 =
                           let uu____13029 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13049 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13049
                              in
                           let uu____13058 =
                             let uu____13067 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13087 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13087
                                in
                             [uu____13067]  in
                           uu____13029 :: uu____13058  in
                         uu____12993 :: uu____13020  in
                       comb_or uu____12984))
                 | (uu____13118,uu____13119,uu____13120,FStar_Pervasives_Native.Some
                    uu____13121) ->
                     (log_unfolding cfg
                        (fun uu____13189  ->
                           let uu____13190 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13190);
                      (let uu____13191 =
                         let uu____13200 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13220 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13220
                            in
                         let uu____13227 =
                           let uu____13236 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13256 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13256
                              in
                           let uu____13265 =
                             let uu____13274 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13294 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13294
                                in
                             [uu____13274]  in
                           uu____13236 :: uu____13265  in
                         uu____13200 :: uu____13227  in
                       comb_or uu____13191))
                 | uu____13325 ->
                     (log_unfolding cfg
                        (fun uu____13371  ->
                           let uu____13372 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____13373 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____13374 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____13372 uu____13373 uu____13374);
                      (let uu____13375 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___251_13379  ->
                                 match uu___251_13379 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____13375))
                  in
               log_unfolding cfg
                 (fun uu____13392  ->
                    let uu____13393 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____13394 = FStar_Range.string_of_range rng  in
                    let uu____13395 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____13393 uu____13394 uu____13395);
               (match res with
                | (false ,uu____13404,uu____13405) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___311_13421 = cfg  in
                      {
                        steps =
                          (let uu___312_13424 = cfg.steps  in
                           {
                             beta = (uu___312_13424.beta);
                             iota = (uu___312_13424.iota);
                             zeta = (uu___312_13424.zeta);
                             weak = (uu___312_13424.weak);
                             hnf = (uu___312_13424.hnf);
                             primops = (uu___312_13424.primops);
                             do_not_unfold_pure_lets =
                               (uu___312_13424.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___312_13424.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___312_13424.pure_subterms_within_computations);
                             simplify = (uu___312_13424.simplify);
                             erase_universes =
                               (uu___312_13424.erase_universes);
                             allow_unbound_universes =
                               (uu___312_13424.allow_unbound_universes);
                             reify_ = (uu___312_13424.reify_);
                             compress_uvars = (uu___312_13424.compress_uvars);
                             no_full_norm = (uu___312_13424.no_full_norm);
                             check_no_uvars = (uu___312_13424.check_no_uvars);
                             unmeta = (uu___312_13424.unmeta);
                             unascribe = (uu___312_13424.unascribe);
                             in_full_norm_request =
                               (uu___312_13424.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___312_13424.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___311_13421.tcenv);
                        debug = (uu___311_13421.debug);
                        delta_level = (uu___311_13421.delta_level);
                        primitive_steps = (uu___311_13421.primitive_steps);
                        strong = (uu___311_13421.strong);
                        memoize_lazy = (uu___311_13421.memoize_lazy);
                        normalize_pure_lets =
                          (uu___311_13421.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____13442 =
                      let uu____13449 = FStar_List.tl stack  in
                      (cfg, uu____13449)  in
                    FStar_Pervasives_Native.Some uu____13442
                | uu____13460 ->
                    let uu____13467 =
                      let uu____13468 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____13468
                       in
                    FStar_All.pipe_left failwith uu____13467))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13776 ->
                   let uu____13799 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13799
               | uu____13800 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13808  ->
               let uu____13809 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13810 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13811 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13818 =
                 let uu____13819 =
                   let uu____13822 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13822
                    in
                 stack_to_string uu____13819  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13809 uu____13810 uu____13811 uu____13818);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____13848  ->
                     let uu____13849 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13849);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____13850 ->
               (log_unfolding cfg
                  (fun uu____13854  ->
                     let uu____13855 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13855);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____13856 ->
               (log_unfolding cfg
                  (fun uu____13860  ->
                     let uu____13861 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13861);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____13862 ->
               (log_unfolding cfg
                  (fun uu____13866  ->
                     let uu____13867 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13867);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13868;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____13869;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____13875  ->
                     let uu____13876 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13876);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13877;
                 FStar_Syntax_Syntax.fv_delta = uu____13878;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____13882  ->
                     let uu____13883 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13883);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13884;
                 FStar_Syntax_Syntax.fv_delta = uu____13885;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13886);_}
               ->
               (log_unfolding cfg
                  (fun uu____13896  ->
                     let uu____13897 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____13897);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____13900 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____13900  in
               let uu____13901 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____13901 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____13934 ->
               let uu____13941 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13941
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____13971 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____13971)
               ->
               let cfg' =
                 let uu___313_13973 = cfg  in
                 {
                   steps =
                     (let uu___314_13976 = cfg.steps  in
                      {
                        beta = (uu___314_13976.beta);
                        iota = (uu___314_13976.iota);
                        zeta = (uu___314_13976.zeta);
                        weak = (uu___314_13976.weak);
                        hnf = (uu___314_13976.hnf);
                        primops = (uu___314_13976.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___314_13976.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___314_13976.unfold_attr);
                        unfold_tac = (uu___314_13976.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___314_13976.pure_subterms_within_computations);
                        simplify = (uu___314_13976.simplify);
                        erase_universes = (uu___314_13976.erase_universes);
                        allow_unbound_universes =
                          (uu___314_13976.allow_unbound_universes);
                        reify_ = (uu___314_13976.reify_);
                        compress_uvars = (uu___314_13976.compress_uvars);
                        no_full_norm = (uu___314_13976.no_full_norm);
                        check_no_uvars = (uu___314_13976.check_no_uvars);
                        unmeta = (uu___314_13976.unmeta);
                        unascribe = (uu___314_13976.unascribe);
                        in_full_norm_request =
                          (uu___314_13976.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___314_13976.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___313_13973.tcenv);
                   debug = (uu___313_13973.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___313_13973.primitive_steps);
                   strong = (uu___313_13973.strong);
                   memoize_lazy = (uu___313_13973.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13981 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____13981 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14010  ->
                              fun stack1  ->
                                match uu____14010 with
                                | (a,aq) ->
                                    let uu____14022 =
                                      let uu____14023 =
                                        let uu____14030 =
                                          let uu____14031 =
                                            let uu____14062 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14062, false)  in
                                          Clos uu____14031  in
                                        (uu____14030, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14023  in
                                    uu____14022 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14150  ->
                          let uu____14151 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14151);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14173 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___252_14178  ->
                                match uu___252_14178 with
                                | UnfoldUntil uu____14179 -> true
                                | UnfoldOnly uu____14180 -> true
                                | UnfoldFully uu____14183 -> true
                                | uu____14186 -> false))
                         in
                      if uu____14173
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___315_14191 = cfg  in
                      let uu____14192 =
                        let uu___316_14193 = to_fsteps s  in
                        {
                          beta = (uu___316_14193.beta);
                          iota = (uu___316_14193.iota);
                          zeta = (uu___316_14193.zeta);
                          weak = (uu___316_14193.weak);
                          hnf = (uu___316_14193.hnf);
                          primops = (uu___316_14193.primops);
                          do_not_unfold_pure_lets =
                            (uu___316_14193.do_not_unfold_pure_lets);
                          unfold_until = (uu___316_14193.unfold_until);
                          unfold_only = (uu___316_14193.unfold_only);
                          unfold_fully = (uu___316_14193.unfold_fully);
                          unfold_attr = (uu___316_14193.unfold_attr);
                          unfold_tac = (uu___316_14193.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___316_14193.pure_subterms_within_computations);
                          simplify = (uu___316_14193.simplify);
                          erase_universes = (uu___316_14193.erase_universes);
                          allow_unbound_universes =
                            (uu___316_14193.allow_unbound_universes);
                          reify_ = (uu___316_14193.reify_);
                          compress_uvars = (uu___316_14193.compress_uvars);
                          no_full_norm = (uu___316_14193.no_full_norm);
                          check_no_uvars = (uu___316_14193.check_no_uvars);
                          unmeta = (uu___316_14193.unmeta);
                          unascribe = (uu___316_14193.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___316_14193.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14192;
                        tcenv = (uu___315_14191.tcenv);
                        debug = (uu___315_14191.debug);
                        delta_level;
                        primitive_steps = (uu___315_14191.primitive_steps);
                        strong = (uu___315_14191.strong);
                        memoize_lazy = (uu___315_14191.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14198 =
                          let uu____14199 =
                            let uu____14204 = FStar_Util.now ()  in
                            (t1, uu____14204)  in
                          Debug uu____14199  in
                        uu____14198 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14208 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14208
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14217 =
                      let uu____14224 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14224, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14217  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14233 = lookup_bvar env x  in
               (match uu____14233 with
                | Univ uu____14234 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14283 = FStar_ST.op_Bang r  in
                      (match uu____14283 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14405  ->
                                 let uu____14406 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14407 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14406
                                   uu____14407);
                            (let uu____14408 = maybe_weakly_reduced t'  in
                             if uu____14408
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14409 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14480)::uu____14481 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14491,uu____14492))::stack_rest ->
                    (match c with
                     | Univ uu____14496 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14505 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14526  ->
                                    let uu____14527 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14527);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14555  ->
                                    let uu____14556 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14556);
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
                       (fun uu____14622  ->
                          let uu____14623 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14623);
                     norm cfg env stack1 t1)
                | (Match uu____14624)::uu____14625 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_14639 = cfg.steps  in
                             {
                               beta = (uu___317_14639.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_14639.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_14639.unfold_until);
                               unfold_only = (uu___317_14639.unfold_only);
                               unfold_fully = (uu___317_14639.unfold_fully);
                               unfold_attr = (uu___317_14639.unfold_attr);
                               unfold_tac = (uu___317_14639.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_14639.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_14639.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_14639.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_14639.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_14639.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_14639.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_14641 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_14641.tcenv);
                               debug = (uu___318_14641.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_14641.primitive_steps);
                               strong = (uu___318_14641.strong);
                               memoize_lazy = (uu___318_14641.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_14641.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14643 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14643 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14675  -> dummy :: env1) env)
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
                                          let uu____14716 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14716)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_14723 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_14723.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_14723.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14724 -> lopt  in
                           (log cfg
                              (fun uu____14730  ->
                                 let uu____14731 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14731);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_14740 = cfg  in
                               {
                                 steps = (uu___320_14740.steps);
                                 tcenv = (uu___320_14740.tcenv);
                                 debug = (uu___320_14740.debug);
                                 delta_level = (uu___320_14740.delta_level);
                                 primitive_steps =
                                   (uu___320_14740.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_14740.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_14740.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____14743)::uu____14744 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_14754 = cfg.steps  in
                             {
                               beta = (uu___317_14754.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_14754.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_14754.unfold_until);
                               unfold_only = (uu___317_14754.unfold_only);
                               unfold_fully = (uu___317_14754.unfold_fully);
                               unfold_attr = (uu___317_14754.unfold_attr);
                               unfold_tac = (uu___317_14754.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_14754.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_14754.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_14754.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_14754.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_14754.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_14754.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_14756 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_14756.tcenv);
                               debug = (uu___318_14756.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_14756.primitive_steps);
                               strong = (uu___318_14756.strong);
                               memoize_lazy = (uu___318_14756.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_14756.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14758 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14758 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14790  -> dummy :: env1) env)
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
                                          let uu____14831 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14831)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_14838 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_14838.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_14838.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14839 -> lopt  in
                           (log cfg
                              (fun uu____14845  ->
                                 let uu____14846 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14846);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_14855 = cfg  in
                               {
                                 steps = (uu___320_14855.steps);
                                 tcenv = (uu___320_14855.tcenv);
                                 debug = (uu___320_14855.debug);
                                 delta_level = (uu___320_14855.delta_level);
                                 primitive_steps =
                                   (uu___320_14855.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_14855.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_14855.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14858)::uu____14859 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_14871 = cfg.steps  in
                             {
                               beta = (uu___317_14871.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_14871.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_14871.unfold_until);
                               unfold_only = (uu___317_14871.unfold_only);
                               unfold_fully = (uu___317_14871.unfold_fully);
                               unfold_attr = (uu___317_14871.unfold_attr);
                               unfold_tac = (uu___317_14871.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_14871.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_14871.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_14871.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_14871.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_14871.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_14871.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_14873 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_14873.tcenv);
                               debug = (uu___318_14873.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_14873.primitive_steps);
                               strong = (uu___318_14873.strong);
                               memoize_lazy = (uu___318_14873.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_14873.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14875 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14875 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14907  -> dummy :: env1) env)
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
                                          let uu____14948 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14948)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_14955 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_14955.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_14955.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14956 -> lopt  in
                           (log cfg
                              (fun uu____14962  ->
                                 let uu____14963 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14963);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_14972 = cfg  in
                               {
                                 steps = (uu___320_14972.steps);
                                 tcenv = (uu___320_14972.tcenv);
                                 debug = (uu___320_14972.debug);
                                 delta_level = (uu___320_14972.delta_level);
                                 primitive_steps =
                                   (uu___320_14972.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_14972.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_14972.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14975)::uu____14976 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_14990 = cfg.steps  in
                             {
                               beta = (uu___317_14990.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_14990.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_14990.unfold_until);
                               unfold_only = (uu___317_14990.unfold_only);
                               unfold_fully = (uu___317_14990.unfold_fully);
                               unfold_attr = (uu___317_14990.unfold_attr);
                               unfold_tac = (uu___317_14990.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_14990.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_14990.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_14990.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_14990.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_14990.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_14990.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_14992 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_14992.tcenv);
                               debug = (uu___318_14992.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_14992.primitive_steps);
                               strong = (uu___318_14992.strong);
                               memoize_lazy = (uu___318_14992.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_14992.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____14994 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14994 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15026  -> dummy :: env1) env)
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
                                          let uu____15067 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15067)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15074 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15074.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15074.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15075 -> lopt  in
                           (log cfg
                              (fun uu____15081  ->
                                 let uu____15082 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15082);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15091 = cfg  in
                               {
                                 steps = (uu___320_15091.steps);
                                 tcenv = (uu___320_15091.tcenv);
                                 debug = (uu___320_15091.debug);
                                 delta_level = (uu___320_15091.delta_level);
                                 primitive_steps =
                                   (uu___320_15091.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15091.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15091.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15094)::uu____15095 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15109 = cfg.steps  in
                             {
                               beta = (uu___317_15109.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15109.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15109.unfold_until);
                               unfold_only = (uu___317_15109.unfold_only);
                               unfold_fully = (uu___317_15109.unfold_fully);
                               unfold_attr = (uu___317_15109.unfold_attr);
                               unfold_tac = (uu___317_15109.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15109.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15109.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15109.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15109.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15109.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15109.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15111 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15111.tcenv);
                               debug = (uu___318_15111.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15111.primitive_steps);
                               strong = (uu___318_15111.strong);
                               memoize_lazy = (uu___318_15111.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15111.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15113 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15113 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15145  -> dummy :: env1) env)
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
                                          let uu____15186 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15186)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15193 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15193.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15193.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15194 -> lopt  in
                           (log cfg
                              (fun uu____15200  ->
                                 let uu____15201 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15201);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15210 = cfg  in
                               {
                                 steps = (uu___320_15210.steps);
                                 tcenv = (uu___320_15210.tcenv);
                                 debug = (uu___320_15210.debug);
                                 delta_level = (uu___320_15210.delta_level);
                                 primitive_steps =
                                   (uu___320_15210.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15210.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15210.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15213)::uu____15214 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15232 = cfg.steps  in
                             {
                               beta = (uu___317_15232.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15232.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15232.unfold_until);
                               unfold_only = (uu___317_15232.unfold_only);
                               unfold_fully = (uu___317_15232.unfold_fully);
                               unfold_attr = (uu___317_15232.unfold_attr);
                               unfold_tac = (uu___317_15232.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15232.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15232.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15232.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15232.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15232.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15232.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15234 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15234.tcenv);
                               debug = (uu___318_15234.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15234.primitive_steps);
                               strong = (uu___318_15234.strong);
                               memoize_lazy = (uu___318_15234.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15234.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15236 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15236 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15268  -> dummy :: env1) env)
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
                                          let uu____15309 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15309)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15316 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15316.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15316.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15317 -> lopt  in
                           (log cfg
                              (fun uu____15323  ->
                                 let uu____15324 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15324);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15333 = cfg  in
                               {
                                 steps = (uu___320_15333.steps);
                                 tcenv = (uu___320_15333.tcenv);
                                 debug = (uu___320_15333.debug);
                                 delta_level = (uu___320_15333.delta_level);
                                 primitive_steps =
                                   (uu___320_15333.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15333.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15333.normalize_pure_lets)
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
                             let uu___317_15339 = cfg.steps  in
                             {
                               beta = (uu___317_15339.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15339.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15339.unfold_until);
                               unfold_only = (uu___317_15339.unfold_only);
                               unfold_fully = (uu___317_15339.unfold_fully);
                               unfold_attr = (uu___317_15339.unfold_attr);
                               unfold_tac = (uu___317_15339.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15339.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15339.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15339.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15339.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15339.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15339.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15341 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15341.tcenv);
                               debug = (uu___318_15341.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15341.primitive_steps);
                               strong = (uu___318_15341.strong);
                               memoize_lazy = (uu___318_15341.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15341.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15343 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15343 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15375  -> dummy :: env1) env)
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
                                          let uu____15416 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15416)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15423 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15423.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15423.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15424 -> lopt  in
                           (log cfg
                              (fun uu____15430  ->
                                 let uu____15431 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15431);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15440 = cfg  in
                               {
                                 steps = (uu___320_15440.steps);
                                 tcenv = (uu___320_15440.tcenv);
                                 debug = (uu___320_15440.debug);
                                 delta_level = (uu___320_15440.delta_level);
                                 primitive_steps =
                                   (uu___320_15440.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15440.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15440.normalize_pure_lets)
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
                      (fun uu____15479  ->
                         fun stack1  ->
                           match uu____15479 with
                           | (a,aq) ->
                               let uu____15491 =
                                 let uu____15492 =
                                   let uu____15499 =
                                     let uu____15500 =
                                       let uu____15531 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15531, false)  in
                                     Clos uu____15500  in
                                   (uu____15499, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15492  in
                               uu____15491 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15619  ->
                     let uu____15620 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15620);
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
                             ((let uu___321_15666 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___321_15666.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___321_15666.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15667 ->
                      let uu____15682 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15682)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15685 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15685 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15710 =
                          let uu____15711 =
                            let uu____15718 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___322_15724 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___322_15724.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___322_15724.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15718)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15711  in
                        mk uu____15710 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15743 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15743
               else
                 (let uu____15745 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15745 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15753 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15775  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15753 c1  in
                      let t2 =
                        let uu____15797 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15797 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15908)::uu____15909 ->
                    (log cfg
                       (fun uu____15922  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15923)::uu____15924 ->
                    (log cfg
                       (fun uu____15935  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15936,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15937;
                                   FStar_Syntax_Syntax.vars = uu____15938;_},uu____15939,uu____15940))::uu____15941
                    ->
                    (log cfg
                       (fun uu____15948  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15949)::uu____15950 ->
                    (log cfg
                       (fun uu____15961  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15962 ->
                    (log cfg
                       (fun uu____15965  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15969  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15994 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15994
                         | FStar_Util.Inr c ->
                             let uu____16008 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16008
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16031 =
                               let uu____16032 =
                                 let uu____16059 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16059, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16032
                                in
                             mk uu____16031 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16094 ->
                           let uu____16095 =
                             let uu____16096 =
                               let uu____16097 =
                                 let uu____16124 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16124, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16097
                                in
                             mk uu____16096 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16095))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___323_16201 = cfg  in
                   {
                     steps =
                       (let uu___324_16204 = cfg.steps  in
                        {
                          beta = (uu___324_16204.beta);
                          iota = (uu___324_16204.iota);
                          zeta = (uu___324_16204.zeta);
                          weak = true;
                          hnf = (uu___324_16204.hnf);
                          primops = (uu___324_16204.primops);
                          do_not_unfold_pure_lets =
                            (uu___324_16204.do_not_unfold_pure_lets);
                          unfold_until = (uu___324_16204.unfold_until);
                          unfold_only = (uu___324_16204.unfold_only);
                          unfold_fully = (uu___324_16204.unfold_fully);
                          unfold_attr = (uu___324_16204.unfold_attr);
                          unfold_tac = (uu___324_16204.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___324_16204.pure_subterms_within_computations);
                          simplify = (uu___324_16204.simplify);
                          erase_universes = (uu___324_16204.erase_universes);
                          allow_unbound_universes =
                            (uu___324_16204.allow_unbound_universes);
                          reify_ = (uu___324_16204.reify_);
                          compress_uvars = (uu___324_16204.compress_uvars);
                          no_full_norm = (uu___324_16204.no_full_norm);
                          check_no_uvars = (uu___324_16204.check_no_uvars);
                          unmeta = (uu___324_16204.unmeta);
                          unascribe = (uu___324_16204.unascribe);
                          in_full_norm_request =
                            (uu___324_16204.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___324_16204.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___323_16201.tcenv);
                     debug = (uu___323_16201.debug);
                     delta_level = (uu___323_16201.delta_level);
                     primitive_steps = (uu___323_16201.primitive_steps);
                     strong = (uu___323_16201.strong);
                     memoize_lazy = (uu___323_16201.memoize_lazy);
                     normalize_pure_lets =
                       (uu___323_16201.normalize_pure_lets)
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
                         let uu____16240 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16240 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___325_16260 = cfg  in
                               let uu____16261 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___325_16260.steps);
                                 tcenv = uu____16261;
                                 debug = (uu___325_16260.debug);
                                 delta_level = (uu___325_16260.delta_level);
                                 primitive_steps =
                                   (uu___325_16260.primitive_steps);
                                 strong = (uu___325_16260.strong);
                                 memoize_lazy = (uu___325_16260.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___325_16260.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16268 =
                                 let uu____16269 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16269  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16268
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___326_16272 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___326_16272.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___326_16272.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___326_16272.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___326_16272.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16273 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16273
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16284,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16285;
                               FStar_Syntax_Syntax.lbunivs = uu____16286;
                               FStar_Syntax_Syntax.lbtyp = uu____16287;
                               FStar_Syntax_Syntax.lbeff = uu____16288;
                               FStar_Syntax_Syntax.lbdef = uu____16289;
                               FStar_Syntax_Syntax.lbattrs = uu____16290;
                               FStar_Syntax_Syntax.lbpos = uu____16291;_}::uu____16292),uu____16293)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16333 =
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
               if uu____16333
               then
                 let binder =
                   let uu____16335 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16335  in
                 let env1 =
                   let uu____16345 =
                     let uu____16352 =
                       let uu____16353 =
                         let uu____16384 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16384,
                           false)
                          in
                       Clos uu____16353  in
                     ((FStar_Pervasives_Native.Some binder), uu____16352)  in
                   uu____16345 :: env  in
                 (log cfg
                    (fun uu____16479  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16483  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16484 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16484))
                 else
                   (let uu____16486 =
                      let uu____16491 =
                        let uu____16492 =
                          let uu____16497 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16497
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16492]  in
                      FStar_Syntax_Subst.open_term uu____16491 body  in
                    match uu____16486 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16518  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16526 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16526  in
                            FStar_Util.Inl
                              (let uu___327_16536 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___327_16536.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___327_16536.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16539  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___328_16541 = lb  in
                             let uu____16542 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___328_16541.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___328_16541.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16542;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___328_16541.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___328_16541.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16567  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___329_16590 = cfg  in
                             {
                               steps = (uu___329_16590.steps);
                               tcenv = (uu___329_16590.tcenv);
                               debug = (uu___329_16590.debug);
                               delta_level = (uu___329_16590.delta_level);
                               primitive_steps =
                                 (uu___329_16590.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___329_16590.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___329_16590.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16593  ->
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
               let uu____16610 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16610 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16646 =
                               let uu___330_16647 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___330_16647.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___330_16647.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16646  in
                           let uu____16648 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16648 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16674 =
                                   FStar_List.map (fun uu____16690  -> dummy)
                                     lbs1
                                    in
                                 let uu____16691 =
                                   let uu____16700 =
                                     FStar_List.map
                                       (fun uu____16720  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16700 env  in
                                 FStar_List.append uu____16674 uu____16691
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16744 =
                                       let uu___331_16745 = rc  in
                                       let uu____16746 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___331_16745.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16746;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___331_16745.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16744
                                 | uu____16755 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___332_16761 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___332_16761.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___332_16761.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___332_16761.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___332_16761.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16771 =
                        FStar_List.map (fun uu____16787  -> dummy) lbs2  in
                      FStar_List.append uu____16771 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16795 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16795 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___333_16811 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___333_16811.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___333_16811.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16840 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16840
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16859 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16935  ->
                        match uu____16935 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___334_17056 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___334_17056.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___334_17056.FStar_Syntax_Syntax.sort)
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
               (match uu____16859 with
                | (rec_env,memos,uu____17283) ->
                    let uu____17336 =
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
                             let uu____17659 =
                               let uu____17666 =
                                 let uu____17667 =
                                   let uu____17698 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17698, false)
                                    in
                                 Clos uu____17667  in
                               (FStar_Pervasives_Native.None, uu____17666)
                                in
                             uu____17659 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17802  ->
                     let uu____17803 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17803);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____17825 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17827::uu____17828 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17833) ->
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
                             | uu____17856 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17870 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17870
                              | uu____17881 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17887 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17911 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17925 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17938 =
                        let uu____17939 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17940 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17939 uu____17940
                         in
                      failwith uu____17938
                    else
                      (let uu____17942 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____17942)
                | uu____17943 -> norm cfg env stack t2))

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
              let uu____17952 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17952 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____17966  ->
                        let uu____17967 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____17967);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____17978  ->
                        let uu____17979 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17980 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____17979 uu____17980);
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
                      | (UnivArgs (us',uu____17993))::stack1 ->
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
                      | uu____18032 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____18035 ->
                          let uu____18038 =
                            let uu____18039 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____18039
                             in
                          failwith uu____18038
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
                  let uu___335_18063 = cfg  in
                  let uu____18064 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18064;
                    tcenv = (uu___335_18063.tcenv);
                    debug = (uu___335_18063.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___335_18063.primitive_steps);
                    strong = (uu___335_18063.strong);
                    memoize_lazy = (uu___335_18063.memoize_lazy);
                    normalize_pure_lets =
                      (uu___335_18063.normalize_pure_lets)
                  }
                else
                  (let uu___336_18066 = cfg  in
                   {
                     steps =
                       (let uu___337_18069 = cfg.steps  in
                        {
                          beta = (uu___337_18069.beta);
                          iota = (uu___337_18069.iota);
                          zeta = false;
                          weak = (uu___337_18069.weak);
                          hnf = (uu___337_18069.hnf);
                          primops = (uu___337_18069.primops);
                          do_not_unfold_pure_lets =
                            (uu___337_18069.do_not_unfold_pure_lets);
                          unfold_until = (uu___337_18069.unfold_until);
                          unfold_only = (uu___337_18069.unfold_only);
                          unfold_fully = (uu___337_18069.unfold_fully);
                          unfold_attr = (uu___337_18069.unfold_attr);
                          unfold_tac = (uu___337_18069.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___337_18069.pure_subterms_within_computations);
                          simplify = (uu___337_18069.simplify);
                          erase_universes = (uu___337_18069.erase_universes);
                          allow_unbound_universes =
                            (uu___337_18069.allow_unbound_universes);
                          reify_ = (uu___337_18069.reify_);
                          compress_uvars = (uu___337_18069.compress_uvars);
                          no_full_norm = (uu___337_18069.no_full_norm);
                          check_no_uvars = (uu___337_18069.check_no_uvars);
                          unmeta = (uu___337_18069.unmeta);
                          unascribe = (uu___337_18069.unascribe);
                          in_full_norm_request =
                            (uu___337_18069.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___337_18069.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___336_18066.tcenv);
                     debug = (uu___336_18066.debug);
                     delta_level = (uu___336_18066.delta_level);
                     primitive_steps = (uu___336_18066.primitive_steps);
                     strong = (uu___336_18066.strong);
                     memoize_lazy = (uu___336_18066.memoize_lazy);
                     normalize_pure_lets =
                       (uu___336_18066.normalize_pure_lets)
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
                  (fun uu____18103  ->
                     let uu____18104 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18105 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18104
                       uu____18105);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18107 =
                   let uu____18108 = FStar_Syntax_Subst.compress head3  in
                   uu____18108.FStar_Syntax_Syntax.n  in
                 match uu____18107 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18126 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18126
                        in
                     let uu____18127 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18127 with
                      | (uu____18128,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18138 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18148 =
                                   let uu____18149 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18149.FStar_Syntax_Syntax.n  in
                                 match uu____18148 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18155,uu____18156))
                                     ->
                                     let uu____18165 =
                                       let uu____18166 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18166.FStar_Syntax_Syntax.n  in
                                     (match uu____18165 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18172,msrc,uu____18174))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18183 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18183
                                      | uu____18184 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18185 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18186 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18186 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___338_18191 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___338_18191.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___338_18191.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___338_18191.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___338_18191.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___338_18191.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18192 = FStar_List.tl stack  in
                                    let uu____18193 =
                                      let uu____18194 =
                                        let uu____18201 =
                                          let uu____18202 =
                                            let uu____18215 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18215)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18202
                                           in
                                        FStar_Syntax_Syntax.mk uu____18201
                                         in
                                      uu____18194
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18192 uu____18193
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18231 =
                                      let uu____18232 = is_return body  in
                                      match uu____18232 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18236;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18237;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18240 -> false  in
                                    if uu____18231
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
                                         let uu____18261 =
                                           let uu____18268 =
                                             let uu____18269 =
                                               let uu____18286 =
                                                 let uu____18293 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18293]  in
                                               (uu____18286, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18269
                                              in
                                           FStar_Syntax_Syntax.mk uu____18268
                                            in
                                         uu____18261
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18327 =
                                           let uu____18328 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18328.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18327 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18334::uu____18335::[])
                                             ->
                                             let uu____18340 =
                                               let uu____18347 =
                                                 let uu____18348 =
                                                   let uu____18355 =
                                                     let uu____18356 =
                                                       let uu____18357 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18357
                                                        in
                                                     let uu____18358 =
                                                       let uu____18361 =
                                                         let uu____18362 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18362
                                                          in
                                                       [uu____18361]  in
                                                     uu____18356 ::
                                                       uu____18358
                                                      in
                                                   (bind1, uu____18355)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18348
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18347
                                                in
                                             uu____18340
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18368 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18380 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18380
                                         then
                                           let uu____18389 =
                                             let uu____18396 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18396
                                              in
                                           let uu____18397 =
                                             let uu____18406 =
                                               let uu____18413 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18413
                                                in
                                             [uu____18406]  in
                                           uu____18389 :: uu____18397
                                         else []  in
                                       let reified =
                                         let uu____18442 =
                                           let uu____18449 =
                                             let uu____18450 =
                                               let uu____18465 =
                                                 let uu____18474 =
                                                   let uu____18483 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18490 =
                                                     let uu____18499 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18499]  in
                                                   uu____18483 :: uu____18490
                                                    in
                                                 let uu____18524 =
                                                   let uu____18533 =
                                                     let uu____18542 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18549 =
                                                       let uu____18558 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18565 =
                                                         let uu____18574 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18581 =
                                                           let uu____18590 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18590]  in
                                                         uu____18574 ::
                                                           uu____18581
                                                          in
                                                       uu____18558 ::
                                                         uu____18565
                                                        in
                                                     uu____18542 ::
                                                       uu____18549
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18533
                                                    in
                                                 FStar_List.append
                                                   uu____18474 uu____18524
                                                  in
                                               (bind_inst, uu____18465)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18450
                                              in
                                           FStar_Syntax_Syntax.mk uu____18449
                                            in
                                         uu____18442
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18656  ->
                                            let uu____18657 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18658 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18657 uu____18658);
                                       (let uu____18659 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18659 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18683 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18683
                        in
                     let uu____18684 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18684 with
                      | (uu____18685,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18722 =
                                  let uu____18723 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18723.FStar_Syntax_Syntax.n  in
                                match uu____18722 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18727) -> t2
                                | uu____18732 -> head4  in
                              let uu____18733 =
                                let uu____18734 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18734.FStar_Syntax_Syntax.n  in
                              match uu____18733 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18740 -> FStar_Pervasives_Native.None
                               in
                            let uu____18741 = maybe_extract_fv head4  in
                            match uu____18741 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18751 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18751
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18756 = maybe_extract_fv head5
                                     in
                                  match uu____18756 with
                                  | FStar_Pervasives_Native.Some uu____18761
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18762 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18767 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18782 =
                              match uu____18782 with
                              | (e,q) ->
                                  let uu____18789 =
                                    let uu____18790 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18790.FStar_Syntax_Syntax.n  in
                                  (match uu____18789 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____18805 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____18805
                                   | uu____18806 -> false)
                               in
                            let uu____18807 =
                              let uu____18808 =
                                let uu____18817 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18817 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18808
                               in
                            if uu____18807
                            then
                              let uu____18836 =
                                let uu____18837 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18837
                                 in
                              failwith uu____18836
                            else ());
                           (let uu____18839 = maybe_unfold_action head_app
                               in
                            match uu____18839 with
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
                                   (fun uu____18882  ->
                                      let uu____18883 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18884 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18883 uu____18884);
                                 (let uu____18885 = FStar_List.tl stack  in
                                  norm cfg env uu____18885 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18887) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18911 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18911  in
                     (log cfg
                        (fun uu____18915  ->
                           let uu____18916 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18916);
                      (let uu____18917 = FStar_List.tl stack  in
                       norm cfg env uu____18917 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____19038  ->
                               match uu____19038 with
                               | (pat,wopt,tm) ->
                                   let uu____19086 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19086)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19118 = FStar_List.tl stack  in
                     norm cfg env uu____19118 tm
                 | uu____19119 -> fallback ())

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
              (fun uu____19133  ->
                 let uu____19134 = FStar_Ident.string_of_lid msrc  in
                 let uu____19135 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19136 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19134
                   uu____19135 uu____19136);
            (let uu____19137 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19137
             then
               let ed =
                 let uu____19139 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19139  in
               let uu____19140 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19140 with
               | (uu____19141,return_repr) ->
                   let return_inst =
                     let uu____19154 =
                       let uu____19155 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19155.FStar_Syntax_Syntax.n  in
                     match uu____19154 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19161::[]) ->
                         let uu____19166 =
                           let uu____19173 =
                             let uu____19174 =
                               let uu____19181 =
                                 let uu____19182 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19182]  in
                               (return_tm, uu____19181)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19174  in
                           FStar_Syntax_Syntax.mk uu____19173  in
                         uu____19166 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19188 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19191 =
                     let uu____19198 =
                       let uu____19199 =
                         let uu____19214 =
                           let uu____19223 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19230 =
                             let uu____19239 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19239]  in
                           uu____19223 :: uu____19230  in
                         (return_inst, uu____19214)  in
                       FStar_Syntax_Syntax.Tm_app uu____19199  in
                     FStar_Syntax_Syntax.mk uu____19198  in
                   uu____19191 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19278 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19278 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19281 =
                      let uu____19282 = FStar_Ident.text_of_lid msrc  in
                      let uu____19283 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19282 uu____19283
                       in
                    failwith uu____19281
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19284;
                      FStar_TypeChecker_Env.mtarget = uu____19285;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19286;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19308 =
                      let uu____19309 = FStar_Ident.text_of_lid msrc  in
                      let uu____19310 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19309 uu____19310
                       in
                    failwith uu____19308
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19311;
                      FStar_TypeChecker_Env.mtarget = uu____19312;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19313;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____19348 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____19349 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____19348 t FStar_Syntax_Syntax.tun uu____19349))

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
                (fun uu____19405  ->
                   match uu____19405 with
                   | (a,imp) ->
                       let uu____19416 = norm cfg env [] a  in
                       (uu____19416, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____19424  ->
             let uu____19425 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____19426 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____19425 uu____19426);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19450 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____19450
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___339_19453 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___339_19453.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___339_19453.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____19475 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____19475
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___340_19478 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___340_19478.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___340_19478.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____19515  ->
                      match uu____19515 with
                      | (a,i) ->
                          let uu____19526 = norm cfg env [] a  in
                          (uu____19526, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___253_19544  ->
                       match uu___253_19544 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____19548 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____19548
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___341_19556 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___342_19559 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___342_19559.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___341_19556.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___341_19556.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19562  ->
        match uu____19562 with
        | (x,imp) ->
            let uu____19565 =
              let uu___343_19566 = x  in
              let uu____19567 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___343_19566.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___343_19566.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19567
              }  in
            (uu____19565, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19573 =
          FStar_List.fold_left
            (fun uu____19607  ->
               fun b  ->
                 match uu____19607 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19573 with | (nbs,uu____19687) -> FStar_List.rev nbs

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
            let uu____19719 =
              let uu___344_19720 = rc  in
              let uu____19721 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___344_19720.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19721;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___344_19720.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19719
        | uu____19730 -> lopt

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
            (let uu____19751 = FStar_Syntax_Print.term_to_string tm  in
             let uu____19752 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____19751
               uu____19752)
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
          let uu____19774 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____19774
          then tm1
          else
            (let w t =
               let uu___345_19788 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___345_19788.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___345_19788.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____19799 =
                 let uu____19800 = FStar_Syntax_Util.unmeta t  in
                 uu____19800.FStar_Syntax_Syntax.n  in
               match uu____19799 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____19807 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____19856)::args1,(bv,uu____19859)::bs1) ->
                   let uu____19893 =
                     let uu____19894 = FStar_Syntax_Subst.compress t  in
                     uu____19894.FStar_Syntax_Syntax.n  in
                   (match uu____19893 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____19898 -> false)
               | ([],[]) -> true
               | (uu____19919,uu____19920) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____19961 = FStar_Syntax_Print.term_to_string t  in
                  let uu____19962 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____19961
                    uu____19962)
               else ();
               (let uu____19964 = FStar_Syntax_Util.head_and_args' t  in
                match uu____19964 with
                | (hd1,args) ->
                    let uu____19997 =
                      let uu____19998 = FStar_Syntax_Subst.compress hd1  in
                      uu____19998.FStar_Syntax_Syntax.n  in
                    (match uu____19997 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____20005 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____20006 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____20007 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____20005 uu____20006 uu____20007)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____20009 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____20026 = FStar_Syntax_Print.term_to_string t  in
                  let uu____20027 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____20026
                    uu____20027)
               else ();
               (let uu____20029 = FStar_Syntax_Util.is_squash t  in
                match uu____20029 with
                | FStar_Pervasives_Native.Some (uu____20040,t') ->
                    is_applied bs t'
                | uu____20052 ->
                    let uu____20061 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____20061 with
                     | FStar_Pervasives_Native.Some (uu____20072,t') ->
                         is_applied bs t'
                     | uu____20084 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20108 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20108 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20115)::(q,uu____20117)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20145 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20146 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20145 uu____20146)
                    else ();
                    (let uu____20148 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20148 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20153 =
                           let uu____20154 = FStar_Syntax_Subst.compress p
                              in
                           uu____20154.FStar_Syntax_Syntax.n  in
                         (match uu____20153 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20162 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20162))
                          | uu____20165 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20168)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20185 =
                           let uu____20186 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20186.FStar_Syntax_Syntax.n  in
                         (match uu____20185 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20194 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20194))
                          | uu____20197 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20201 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20201 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20206 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20206 with
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
                                     let uu____20217 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20217))
                               | uu____20220 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____20225)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____20242 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____20242 with
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
                                     let uu____20253 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____20253))
                               | uu____20256 -> FStar_Pervasives_Native.None)
                          | uu____20259 -> FStar_Pervasives_Native.None)
                     | uu____20262 -> FStar_Pervasives_Native.None))
               | uu____20265 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____20278 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20278 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____20284)::[],uu____20285,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20296 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____20297 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____20296
                         uu____20297)
                    else ();
                    is_quantified_const bv phi')
               | uu____20299 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____20312 =
                 let uu____20313 = FStar_Syntax_Subst.compress phi  in
                 uu____20313.FStar_Syntax_Syntax.n  in
               match uu____20312 with
               | FStar_Syntax_Syntax.Tm_match (uu____20318,br::brs) ->
                   let uu____20385 = br  in
                   (match uu____20385 with
                    | (uu____20402,uu____20403,e) ->
                        let r =
                          let uu____20424 = simp_t e  in
                          match uu____20424 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____20430 =
                                FStar_List.for_all
                                  (fun uu____20448  ->
                                     match uu____20448 with
                                     | (uu____20461,uu____20462,e') ->
                                         let uu____20476 = simp_t e'  in
                                         uu____20476 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____20430
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____20484 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____20493 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____20493
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____20524 =
                 match uu____20524 with
                 | (t1,q) ->
                     let uu____20537 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____20537 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____20565 -> (t1, q))
                  in
               let uu____20576 = FStar_Syntax_Util.head_and_args t  in
               match uu____20576 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____20642 =
                 let uu____20643 = FStar_Syntax_Util.unmeta ty  in
                 uu____20643.FStar_Syntax_Syntax.n  in
               match uu____20642 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____20647) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____20652,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____20672 -> false  in
             let simplify1 arg =
               let uu____20697 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____20697, arg)  in
             let uu____20706 = is_forall_const tm1  in
             match uu____20706 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____20711 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____20712 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____20711
                       uu____20712)
                  else ();
                  (let uu____20714 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____20714))
             | FStar_Pervasives_Native.None  ->
                 let uu____20715 =
                   let uu____20716 = FStar_Syntax_Subst.compress tm1  in
                   uu____20716.FStar_Syntax_Syntax.n  in
                 (match uu____20715 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____20720;
                              FStar_Syntax_Syntax.vars = uu____20721;_},uu____20722);
                         FStar_Syntax_Syntax.pos = uu____20723;
                         FStar_Syntax_Syntax.vars = uu____20724;_},args)
                      ->
                      let uu____20750 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20750
                      then
                        let uu____20751 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20751 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20796)::
                             (uu____20797,(arg,uu____20799))::[] ->
                             maybe_auto_squash arg
                         | (uu____20848,(arg,uu____20850))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20851)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20900)::uu____20901::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20952::(FStar_Pervasives_Native.Some (false
                                         ),uu____20953)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21004 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21018 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21018
                         then
                           let uu____21019 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21019 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21064)::uu____21065::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21116::(FStar_Pervasives_Native.Some (true
                                           ),uu____21117)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21168)::(uu____21169,(arg,uu____21171))::[]
                               -> maybe_auto_squash arg
                           | (uu____21220,(arg,uu____21222))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21223)::[]
                               -> maybe_auto_squash arg
                           | uu____21272 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21286 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21286
                            then
                              let uu____21287 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21287 with
                              | uu____21332::(FStar_Pervasives_Native.Some
                                              (true ),uu____21333)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21384)::uu____21385::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21436)::(uu____21437,(arg,uu____21439))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21488,(p,uu____21490))::(uu____21491,
                                                                (q,uu____21493))::[]
                                  ->
                                  let uu____21540 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21540
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21542 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21556 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21556
                               then
                                 let uu____21557 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21557 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21602)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21603)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21654)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21655)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21706)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21707)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21758)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21759)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21810,(arg,uu____21812))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21813)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21862)::(uu____21863,(arg,uu____21865))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21914,(arg,uu____21916))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21917)::[]
                                     ->
                                     let uu____21966 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21966
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21967)::(uu____21968,(arg,uu____21970))::[]
                                     ->
                                     let uu____22019 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22019
                                 | (uu____22020,(p,uu____22022))::(uu____22023,
                                                                   (q,uu____22025))::[]
                                     ->
                                     let uu____22072 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22072
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22074 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22088 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22088
                                  then
                                    let uu____22089 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22089 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22134)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22165)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22196 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22210 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22210
                                     then
                                       match args with
                                       | (t,uu____22212)::[] ->
                                           let uu____22229 =
                                             let uu____22230 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22230.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22229 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22233::[],body,uu____22235)
                                                ->
                                                let uu____22262 = simp_t body
                                                   in
                                                (match uu____22262 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22265 -> tm1)
                                            | uu____22268 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22270))::(t,uu____22272)::[]
                                           ->
                                           let uu____22299 =
                                             let uu____22300 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22300.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22299 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22303::[],body,uu____22305)
                                                ->
                                                let uu____22332 = simp_t body
                                                   in
                                                (match uu____22332 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22335 -> tm1)
                                            | uu____22338 -> tm1)
                                       | uu____22339 -> tm1
                                     else
                                       (let uu____22349 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22349
                                        then
                                          match args with
                                          | (t,uu____22351)::[] ->
                                              let uu____22368 =
                                                let uu____22369 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22369.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22368 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22372::[],body,uu____22374)
                                                   ->
                                                   let uu____22401 =
                                                     simp_t body  in
                                                   (match uu____22401 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22404 -> tm1)
                                               | uu____22407 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22409))::(t,uu____22411)::[]
                                              ->
                                              let uu____22438 =
                                                let uu____22439 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22439.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22438 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22442::[],body,uu____22444)
                                                   ->
                                                   let uu____22471 =
                                                     simp_t body  in
                                                   (match uu____22471 with
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
                                                    | uu____22474 -> tm1)
                                               | uu____22477 -> tm1)
                                          | uu____22478 -> tm1
                                        else
                                          (let uu____22488 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22488
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22489;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22490;_},uu____22491)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22508;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22509;_},uu____22510)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22527 -> tm1
                                           else
                                             (let uu____22537 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22537 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22557 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22567;
                         FStar_Syntax_Syntax.vars = uu____22568;_},args)
                      ->
                      let uu____22590 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22590
                      then
                        let uu____22591 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22591 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22636)::
                             (uu____22637,(arg,uu____22639))::[] ->
                             maybe_auto_squash arg
                         | (uu____22688,(arg,uu____22690))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22691)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22740)::uu____22741::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22792::(FStar_Pervasives_Native.Some (false
                                         ),uu____22793)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22844 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22858 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22858
                         then
                           let uu____22859 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22859 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22904)::uu____22905::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22956::(FStar_Pervasives_Native.Some (true
                                           ),uu____22957)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____23008)::(uu____23009,(arg,uu____23011))::[]
                               -> maybe_auto_squash arg
                           | (uu____23060,(arg,uu____23062))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____23063)::[]
                               -> maybe_auto_squash arg
                           | uu____23112 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23126 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23126
                            then
                              let uu____23127 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23127 with
                              | uu____23172::(FStar_Pervasives_Native.Some
                                              (true ),uu____23173)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23224)::uu____23225::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23276)::(uu____23277,(arg,uu____23279))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23328,(p,uu____23330))::(uu____23331,
                                                                (q,uu____23333))::[]
                                  ->
                                  let uu____23380 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23380
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23382 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23396 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23396
                               then
                                 let uu____23397 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23397 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23442)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23443)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23494)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23495)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23546)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23547)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23598)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23599)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23650,(arg,uu____23652))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23653)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23702)::(uu____23703,(arg,uu____23705))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23754,(arg,uu____23756))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23757)::[]
                                     ->
                                     let uu____23806 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23806
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23807)::(uu____23808,(arg,uu____23810))::[]
                                     ->
                                     let uu____23859 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23859
                                 | (uu____23860,(p,uu____23862))::(uu____23863,
                                                                   (q,uu____23865))::[]
                                     ->
                                     let uu____23912 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23912
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23914 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23928 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23928
                                  then
                                    let uu____23929 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23929 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23974)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24005)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24036 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24050 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24050
                                     then
                                       match args with
                                       | (t,uu____24052)::[] ->
                                           let uu____24069 =
                                             let uu____24070 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24070.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24069 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24073::[],body,uu____24075)
                                                ->
                                                let uu____24102 = simp_t body
                                                   in
                                                (match uu____24102 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24105 -> tm1)
                                            | uu____24108 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24110))::(t,uu____24112)::[]
                                           ->
                                           let uu____24139 =
                                             let uu____24140 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24140.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24139 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24143::[],body,uu____24145)
                                                ->
                                                let uu____24172 = simp_t body
                                                   in
                                                (match uu____24172 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24175 -> tm1)
                                            | uu____24178 -> tm1)
                                       | uu____24179 -> tm1
                                     else
                                       (let uu____24189 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24189
                                        then
                                          match args with
                                          | (t,uu____24191)::[] ->
                                              let uu____24208 =
                                                let uu____24209 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24209.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24208 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24212::[],body,uu____24214)
                                                   ->
                                                   let uu____24241 =
                                                     simp_t body  in
                                                   (match uu____24241 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24244 -> tm1)
                                               | uu____24247 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24249))::(t,uu____24251)::[]
                                              ->
                                              let uu____24278 =
                                                let uu____24279 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24279.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24278 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24282::[],body,uu____24284)
                                                   ->
                                                   let uu____24311 =
                                                     simp_t body  in
                                                   (match uu____24311 with
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
                                                    | uu____24314 -> tm1)
                                               | uu____24317 -> tm1)
                                          | uu____24318 -> tm1
                                        else
                                          (let uu____24328 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24328
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24329;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24330;_},uu____24331)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24348;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24349;_},uu____24350)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24367 -> tm1
                                           else
                                             (let uu____24377 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24377 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24397 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24412 = simp_t t  in
                      (match uu____24412 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24415 ->
                      let uu____24438 = is_const_match tm1  in
                      (match uu____24438 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24441 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____24451  ->
               (let uu____24453 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24454 = FStar_Syntax_Print.term_to_string t  in
                let uu____24455 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24462 =
                  let uu____24463 =
                    let uu____24466 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24466
                     in
                  stack_to_string uu____24463  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24453 uu____24454 uu____24455 uu____24462);
               (let uu____24489 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24489
                then
                  let uu____24490 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24490 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24497 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24498 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24499 =
                          let uu____24500 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24500
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24497
                          uu____24498 uu____24499);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____24518 =
                     let uu____24519 =
                       let uu____24520 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____24520  in
                     FStar_Util.string_of_int uu____24519  in
                   let uu____24525 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____24526 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____24518 uu____24525 uu____24526)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____24532,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____24583  ->
                     let uu____24584 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____24584);
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
               let uu____24622 =
                 let uu___346_24623 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___346_24623.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___346_24623.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____24622
           | (Arg (Univ uu____24626,uu____24627,uu____24628))::uu____24629 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____24632,uu____24633))::uu____24634 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____24649,uu____24650),aq,r))::stack1
               when
               let uu____24700 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24700 ->
               let t2 =
                 let uu____24704 =
                   let uu____24709 =
                     let uu____24710 = closure_as_term cfg env_arg tm  in
                     (uu____24710, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____24709  in
                 uu____24704 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____24720),aq,r))::stack1 ->
               (log cfg
                  (fun uu____24773  ->
                     let uu____24774 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____24774);
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
                  (let uu____24786 = FStar_ST.op_Bang m  in
                   match uu____24786 with
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
                   | FStar_Pervasives_Native.Some (uu____24929,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____24982 =
                 log cfg
                   (fun uu____24986  ->
                      let uu____24987 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____24987);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____24993 =
                 let uu____24994 = FStar_Syntax_Subst.compress t1  in
                 uu____24994.FStar_Syntax_Syntax.n  in
               (match uu____24993 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____25021 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____25021  in
                    (log cfg
                       (fun uu____25025  ->
                          let uu____25026 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____25026);
                     (let uu____25027 = FStar_List.tl stack  in
                      norm cfg env1 uu____25027 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____25028);
                       FStar_Syntax_Syntax.pos = uu____25029;
                       FStar_Syntax_Syntax.vars = uu____25030;_},(e,uu____25032)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____25061 when
                    (cfg.steps).primops ->
                    let uu____25076 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____25076 with
                     | (hd1,args) ->
                         let uu____25113 =
                           let uu____25114 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____25114.FStar_Syntax_Syntax.n  in
                         (match uu____25113 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____25118 = find_prim_step cfg fv  in
                              (match uu____25118 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____25121; arity = uu____25122;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____25124;
                                     requires_binder_substitution =
                                       uu____25125;
                                     interpretation = uu____25126;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____25141 -> fallback " (3)" ())
                          | uu____25144 -> fallback " (4)" ()))
                | uu____25145 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____25168  ->
                     let uu____25169 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____25169);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____25178 =
                   log cfg1
                     (fun uu____25183  ->
                        let uu____25184 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____25185 =
                          let uu____25186 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____25213  ->
                                    match uu____25213 with
                                    | (p,uu____25223,uu____25224) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____25186
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____25184 uu____25185);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___254_25241  ->
                                match uu___254_25241 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____25242 -> false))
                         in
                      let steps =
                        let uu___347_25244 = cfg1.steps  in
                        {
                          beta = (uu___347_25244.beta);
                          iota = (uu___347_25244.iota);
                          zeta = false;
                          weak = (uu___347_25244.weak);
                          hnf = (uu___347_25244.hnf);
                          primops = (uu___347_25244.primops);
                          do_not_unfold_pure_lets =
                            (uu___347_25244.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___347_25244.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___347_25244.pure_subterms_within_computations);
                          simplify = (uu___347_25244.simplify);
                          erase_universes = (uu___347_25244.erase_universes);
                          allow_unbound_universes =
                            (uu___347_25244.allow_unbound_universes);
                          reify_ = (uu___347_25244.reify_);
                          compress_uvars = (uu___347_25244.compress_uvars);
                          no_full_norm = (uu___347_25244.no_full_norm);
                          check_no_uvars = (uu___347_25244.check_no_uvars);
                          unmeta = (uu___347_25244.unmeta);
                          unascribe = (uu___347_25244.unascribe);
                          in_full_norm_request =
                            (uu___347_25244.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___347_25244.weakly_reduce_scrutinee)
                        }  in
                      let uu___348_25249 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___348_25249.tcenv);
                        debug = (uu___348_25249.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___348_25249.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___348_25249.memoize_lazy);
                        normalize_pure_lets =
                          (uu___348_25249.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____25321 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____25350 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____25434  ->
                                    fun uu____25435  ->
                                      match (uu____25434, uu____25435) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____25574 = norm_pat env3 p1
                                             in
                                          (match uu____25574 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____25350 with
                           | (pats1,env3) ->
                               ((let uu___349_25736 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___349_25736.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___350_25755 = x  in
                            let uu____25756 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___350_25755.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___350_25755.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25756
                            }  in
                          ((let uu___351_25770 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___351_25770.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___352_25781 = x  in
                            let uu____25782 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___352_25781.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___352_25781.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25782
                            }  in
                          ((let uu___353_25796 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___353_25796.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___354_25812 = x  in
                            let uu____25813 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___354_25812.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___354_25812.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____25813
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___355_25828 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___355_25828.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____25872 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____25902 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____25902 with
                                  | (p,wopt,e) ->
                                      let uu____25922 = norm_pat env1 p  in
                                      (match uu____25922 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____25977 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____25977
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____25994 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____25994
                      then
                        norm
                          (let uu___356_25999 = cfg1  in
                           {
                             steps =
                               (let uu___357_26002 = cfg1.steps  in
                                {
                                  beta = (uu___357_26002.beta);
                                  iota = (uu___357_26002.iota);
                                  zeta = (uu___357_26002.zeta);
                                  weak = (uu___357_26002.weak);
                                  hnf = (uu___357_26002.hnf);
                                  primops = (uu___357_26002.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___357_26002.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___357_26002.unfold_until);
                                  unfold_only = (uu___357_26002.unfold_only);
                                  unfold_fully =
                                    (uu___357_26002.unfold_fully);
                                  unfold_attr = (uu___357_26002.unfold_attr);
                                  unfold_tac = (uu___357_26002.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___357_26002.pure_subterms_within_computations);
                                  simplify = (uu___357_26002.simplify);
                                  erase_universes =
                                    (uu___357_26002.erase_universes);
                                  allow_unbound_universes =
                                    (uu___357_26002.allow_unbound_universes);
                                  reify_ = (uu___357_26002.reify_);
                                  compress_uvars =
                                    (uu___357_26002.compress_uvars);
                                  no_full_norm =
                                    (uu___357_26002.no_full_norm);
                                  check_no_uvars =
                                    (uu___357_26002.check_no_uvars);
                                  unmeta = (uu___357_26002.unmeta);
                                  unascribe = (uu___357_26002.unascribe);
                                  in_full_norm_request =
                                    (uu___357_26002.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___356_25999.tcenv);
                             debug = (uu___356_25999.debug);
                             delta_level = (uu___356_25999.delta_level);
                             primitive_steps =
                               (uu___356_25999.primitive_steps);
                             strong = (uu___356_25999.strong);
                             memoize_lazy = (uu___356_25999.memoize_lazy);
                             normalize_pure_lets =
                               (uu___356_25999.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____26004 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____26004)
                    in
                 let rec is_cons head1 =
                   let uu____26029 =
                     let uu____26030 = FStar_Syntax_Subst.compress head1  in
                     uu____26030.FStar_Syntax_Syntax.n  in
                   match uu____26029 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____26034) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____26039 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____26040;
                         FStar_Syntax_Syntax.fv_delta = uu____26041;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____26042;
                         FStar_Syntax_Syntax.fv_delta = uu____26043;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____26044);_}
                       -> true
                   | uu____26051 -> false  in
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
                   let uu____26214 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____26214 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____26301 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____26340 ->
                                 let uu____26341 =
                                   let uu____26342 = is_cons head1  in
                                   Prims.op_Negation uu____26342  in
                                 FStar_Util.Inr uu____26341)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____26367 =
                              let uu____26368 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____26368.FStar_Syntax_Syntax.n  in
                            (match uu____26367 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____26386 ->
                                 let uu____26387 =
                                   let uu____26388 = is_cons head1  in
                                   Prims.op_Negation uu____26388  in
                                 FStar_Util.Inr uu____26387))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____26465)::rest_a,(p1,uu____26468)::rest_p) ->
                       let uu____26512 = matches_pat t2 p1  in
                       (match uu____26512 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____26561 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____26679 = matches_pat scrutinee1 p1  in
                       (match uu____26679 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____26719  ->
                                  let uu____26720 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____26721 =
                                    let uu____26722 =
                                      FStar_List.map
                                        (fun uu____26732  ->
                                           match uu____26732 with
                                           | (uu____26737,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____26722
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____26720 uu____26721);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____26769  ->
                                       match uu____26769 with
                                       | (bv,t2) ->
                                           let uu____26792 =
                                             let uu____26799 =
                                               let uu____26802 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____26802
                                                in
                                             let uu____26803 =
                                               let uu____26804 =
                                                 let uu____26835 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____26835, false)
                                                  in
                                               Clos uu____26804  in
                                             (uu____26799, uu____26803)  in
                                           uu____26792 :: env2) env1 s
                                 in
                              let uu____26948 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____26948)))
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
    let uu____26975 =
      let uu____26978 = FStar_ST.op_Bang plugins  in p :: uu____26978  in
    FStar_ST.op_Colon_Equals plugins uu____26975  in
  let retrieve uu____27086 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____27163  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___255_27204  ->
                  match uu___255_27204 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | uu____27208 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____27214 -> d  in
        let uu____27217 = to_fsteps s  in
        let uu____27218 =
          let uu____27219 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____27220 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____27221 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____27222 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____27223 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____27224 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____27225 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____27219;
            primop = uu____27220;
            unfolding = uu____27221;
            b380 = uu____27222;
            wpe = uu____27223;
            norm_delayed = uu____27224;
            print_normalized = uu____27225
          }  in
        let uu____27226 =
          let uu____27229 =
            let uu____27232 = retrieve_plugins ()  in
            FStar_List.append uu____27232 psteps  in
          add_steps built_in_primitive_steps uu____27229  in
        let uu____27235 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____27237 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____27237)
           in
        {
          steps = uu____27217;
          tcenv = e;
          debug = uu____27218;
          delta_level = d1;
          primitive_steps = uu____27226;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____27235
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
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config' ps s e  in
          log c
            (fun uu____27286  ->
               let uu____27287 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "Starting normalizer for (%s)\n" uu____27287);
          norm c [] [] t
  
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
      fun t  -> let uu____27324 = config s e  in norm_comp uu____27324 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27341 = config [] env  in norm_universe uu____27341 [] u
  
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
        let uu____27365 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27365  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27372 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___358_27391 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___358_27391.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___358_27391.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27398 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27398
          then
            let ct1 =
              let uu____27400 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27400 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____27407 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27407
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___359_27411 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___359_27411.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___359_27411.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___359_27411.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___360_27413 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___360_27413.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___360_27413.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___360_27413.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___360_27413.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___361_27414 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___361_27414.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___361_27414.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27416 -> c
  
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
        let uu____27434 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____27434  in
      let uu____27441 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____27441
      then
        let uu____27442 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____27442 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____27448  ->
                 let uu____27449 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____27449)
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
            ((let uu____27470 =
                let uu____27475 =
                  let uu____27476 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27476
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27475)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27470);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____27491 = config [AllowUnboundUniverses] env  in
          norm_comp uu____27491 [] c
        with
        | e ->
            ((let uu____27504 =
                let uu____27509 =
                  let uu____27510 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27510
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27509)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27504);
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
                   let uu____27555 =
                     let uu____27556 =
                       let uu____27563 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27563)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27556  in
                   mk uu____27555 t01.FStar_Syntax_Syntax.pos
               | uu____27568 -> t2)
          | uu____27569 -> t2  in
        aux t
  
let (unfold_whnf' :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append steps
             [Primops;
             Weak;
             HNF;
             UnfoldUntil FStar_Syntax_Syntax.delta_constant;
             Beta]) env t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> unfold_whnf' [] env t 
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
        let uu____27648 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27648 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27677 ->
                 let uu____27684 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27684 with
                  | (actuals,uu____27694,uu____27695) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27709 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27709 with
                         | (binders,args) ->
                             let uu____27720 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27720
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
      | uu____27734 ->
          let uu____27735 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27735 with
           | (head1,args) ->
               let uu____27772 =
                 let uu____27773 = FStar_Syntax_Subst.compress head1  in
                 uu____27773.FStar_Syntax_Syntax.n  in
               (match uu____27772 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27794 =
                      let uu____27807 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27807  in
                    (match uu____27794 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27837 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___366_27845 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___366_27845.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___366_27845.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___366_27845.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___366_27845.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___366_27845.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___366_27845.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___366_27845.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___366_27845.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___366_27845.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___366_27845.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___366_27845.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___366_27845.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___366_27845.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___366_27845.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___366_27845.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___366_27845.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___366_27845.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___366_27845.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___366_27845.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___366_27845.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___366_27845.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___366_27845.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___366_27845.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___366_27845.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___366_27845.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___366_27845.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___366_27845.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___366_27845.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___366_27845.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___366_27845.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___366_27845.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___366_27845.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___366_27845.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___366_27845.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___366_27845.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___366_27845.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___366_27845.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____27837 with
                            | (uu____27846,ty,uu____27848) ->
                                eta_expand_with_type env t ty))
                | uu____27849 ->
                    let uu____27850 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___367_27858 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___367_27858.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___367_27858.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___367_27858.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___367_27858.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___367_27858.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___367_27858.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___367_27858.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___367_27858.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___367_27858.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___367_27858.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___367_27858.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___367_27858.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___367_27858.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___367_27858.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___367_27858.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___367_27858.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___367_27858.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___367_27858.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___367_27858.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___367_27858.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___367_27858.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___367_27858.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___367_27858.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___367_27858.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___367_27858.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___367_27858.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___367_27858.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___367_27858.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___367_27858.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___367_27858.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___367_27858.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___367_27858.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___367_27858.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___367_27858.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___367_27858.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___367_27858.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___367_27858.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____27850 with
                     | (uu____27859,ty,uu____27861) ->
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
      let uu___368_27934 = x  in
      let uu____27935 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___368_27934.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___368_27934.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27935
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27938 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27961 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27962 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27963 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27964 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27971 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27972 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27973 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___369_28003 = rc  in
          let uu____28004 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28013 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___369_28003.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28004;
            FStar_Syntax_Syntax.residual_flags = uu____28013
          }  in
        let uu____28016 =
          let uu____28017 =
            let uu____28034 = elim_delayed_subst_binders bs  in
            let uu____28041 = elim_delayed_subst_term t2  in
            let uu____28044 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28034, uu____28041, uu____28044)  in
          FStar_Syntax_Syntax.Tm_abs uu____28017  in
        mk1 uu____28016
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28075 =
          let uu____28076 =
            let uu____28089 = elim_delayed_subst_binders bs  in
            let uu____28096 = elim_delayed_subst_comp c  in
            (uu____28089, uu____28096)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28076  in
        mk1 uu____28075
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28113 =
          let uu____28114 =
            let uu____28121 = elim_bv bv  in
            let uu____28122 = elim_delayed_subst_term phi  in
            (uu____28121, uu____28122)  in
          FStar_Syntax_Syntax.Tm_refine uu____28114  in
        mk1 uu____28113
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28149 =
          let uu____28150 =
            let uu____28165 = elim_delayed_subst_term t2  in
            let uu____28168 = elim_delayed_subst_args args  in
            (uu____28165, uu____28168)  in
          FStar_Syntax_Syntax.Tm_app uu____28150  in
        mk1 uu____28149
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___370_28236 = p  in
              let uu____28237 =
                let uu____28238 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28238  in
              {
                FStar_Syntax_Syntax.v = uu____28237;
                FStar_Syntax_Syntax.p =
                  (uu___370_28236.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___371_28240 = p  in
              let uu____28241 =
                let uu____28242 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28242  in
              {
                FStar_Syntax_Syntax.v = uu____28241;
                FStar_Syntax_Syntax.p =
                  (uu___371_28240.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___372_28249 = p  in
              let uu____28250 =
                let uu____28251 =
                  let uu____28258 = elim_bv x  in
                  let uu____28259 = elim_delayed_subst_term t0  in
                  (uu____28258, uu____28259)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28251  in
              {
                FStar_Syntax_Syntax.v = uu____28250;
                FStar_Syntax_Syntax.p =
                  (uu___372_28249.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___373_28282 = p  in
              let uu____28283 =
                let uu____28284 =
                  let uu____28297 =
                    FStar_List.map
                      (fun uu____28320  ->
                         match uu____28320 with
                         | (x,b) ->
                             let uu____28333 = elim_pat x  in
                             (uu____28333, b)) pats
                     in
                  (fv, uu____28297)  in
                FStar_Syntax_Syntax.Pat_cons uu____28284  in
              {
                FStar_Syntax_Syntax.v = uu____28283;
                FStar_Syntax_Syntax.p =
                  (uu___373_28282.FStar_Syntax_Syntax.p)
              }
          | uu____28346 -> p  in
        let elim_branch uu____28370 =
          match uu____28370 with
          | (pat,wopt,t3) ->
              let uu____28396 = elim_pat pat  in
              let uu____28399 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28402 = elim_delayed_subst_term t3  in
              (uu____28396, uu____28399, uu____28402)
           in
        let uu____28407 =
          let uu____28408 =
            let uu____28431 = elim_delayed_subst_term t2  in
            let uu____28434 = FStar_List.map elim_branch branches  in
            (uu____28431, uu____28434)  in
          FStar_Syntax_Syntax.Tm_match uu____28408  in
        mk1 uu____28407
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28565 =
          match uu____28565 with
          | (tc,topt) ->
              let uu____28600 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28610 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28610
                | FStar_Util.Inr c ->
                    let uu____28612 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28612
                 in
              let uu____28613 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28600, uu____28613)
           in
        let uu____28622 =
          let uu____28623 =
            let uu____28650 = elim_delayed_subst_term t2  in
            let uu____28653 = elim_ascription a  in
            (uu____28650, uu____28653, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28623  in
        mk1 uu____28622
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___374_28714 = lb  in
          let uu____28715 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28718 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___374_28714.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___374_28714.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28715;
            FStar_Syntax_Syntax.lbeff =
              (uu___374_28714.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28718;
            FStar_Syntax_Syntax.lbattrs =
              (uu___374_28714.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___374_28714.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28721 =
          let uu____28722 =
            let uu____28735 =
              let uu____28742 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28742)  in
            let uu____28751 = elim_delayed_subst_term t2  in
            (uu____28735, uu____28751)  in
          FStar_Syntax_Syntax.Tm_let uu____28722  in
        mk1 uu____28721
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28795 =
          let uu____28796 =
            let uu____28803 = elim_delayed_subst_term tm  in
            (uu____28803, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28796  in
        mk1 uu____28795
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28814 =
          let uu____28815 =
            let uu____28822 = elim_delayed_subst_term t2  in
            let uu____28825 = elim_delayed_subst_meta md  in
            (uu____28822, uu____28825)  in
          FStar_Syntax_Syntax.Tm_meta uu____28815  in
        mk1 uu____28814

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___256_28834  ->
         match uu___256_28834 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28838 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28838
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
        let uu____28861 =
          let uu____28862 =
            let uu____28871 = elim_delayed_subst_term t  in
            (uu____28871, uopt)  in
          FStar_Syntax_Syntax.Total uu____28862  in
        mk1 uu____28861
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28888 =
          let uu____28889 =
            let uu____28898 = elim_delayed_subst_term t  in
            (uu____28898, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28889  in
        mk1 uu____28888
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___375_28907 = ct  in
          let uu____28908 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28911 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28920 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___375_28907.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___375_28907.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28908;
            FStar_Syntax_Syntax.effect_args = uu____28911;
            FStar_Syntax_Syntax.flags = uu____28920
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___257_28923  ->
    match uu___257_28923 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____28935 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____28935
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28968 =
          let uu____28975 = elim_delayed_subst_term t  in (m, uu____28975)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28968
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28987 =
          let uu____28996 = elim_delayed_subst_term t  in
          (m1, m2, uu____28996)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28987
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____29023  ->
         match uu____29023 with
         | (t,q) ->
             let uu____29034 = elim_delayed_subst_term t  in (uu____29034, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29054  ->
         match uu____29054 with
         | (x,q) ->
             let uu____29065 =
               let uu___376_29066 = x  in
               let uu____29067 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___376_29066.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___376_29066.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29067
               }  in
             (uu____29065, q)) bs

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
            | (uu____29159,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29185,FStar_Util.Inl t) ->
                let uu____29203 =
                  let uu____29210 =
                    let uu____29211 =
                      let uu____29224 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29224)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29211  in
                  FStar_Syntax_Syntax.mk uu____29210  in
                uu____29203 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29238 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29238 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29268 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29331 ->
                    let uu____29332 =
                      let uu____29341 =
                        let uu____29342 = FStar_Syntax_Subst.compress t4  in
                        uu____29342.FStar_Syntax_Syntax.n  in
                      (uu____29341, tc)  in
                    (match uu____29332 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29369) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29410) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29449,FStar_Util.Inl uu____29450) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29477 -> failwith "Impossible")
                 in
              (match uu____29268 with
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
          let uu____29602 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29602 with
          | (univ_names1,binders1,tc) ->
              let uu____29668 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29668)
  
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
          let uu____29717 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29717 with
          | (univ_names1,binders1,tc) ->
              let uu____29783 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29783)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29822 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29822 with
           | (univ_names1,binders1,typ1) ->
               let uu___377_29856 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___377_29856.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___377_29856.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___377_29856.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___377_29856.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___378_29871 = s  in
          let uu____29872 =
            let uu____29873 =
              let uu____29882 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29882, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29873  in
          {
            FStar_Syntax_Syntax.sigel = uu____29872;
            FStar_Syntax_Syntax.sigrng =
              (uu___378_29871.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___378_29871.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___378_29871.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___378_29871.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29899 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29899 with
           | (univ_names1,uu____29919,typ1) ->
               let uu___379_29937 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_29937.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_29937.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_29937.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_29937.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29943 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29943 with
           | (univ_names1,uu____29963,typ1) ->
               let uu___380_29981 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___380_29981.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___380_29981.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___380_29981.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___380_29981.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30009 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30009 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30034 =
                            let uu____30035 =
                              let uu____30036 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____30036  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30035
                             in
                          elim_delayed_subst_term uu____30034  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___381_30039 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___381_30039.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___381_30039.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___381_30039.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___381_30039.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___382_30040 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___382_30040.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_30040.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_30040.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_30040.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___383_30046 = s  in
          let uu____30047 =
            let uu____30048 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____30048  in
          {
            FStar_Syntax_Syntax.sigel = uu____30047;
            FStar_Syntax_Syntax.sigrng =
              (uu___383_30046.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___383_30046.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___383_30046.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___383_30046.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30052 = elim_uvars_aux_t env us [] t  in
          (match uu____30052 with
           | (us1,uu____30072,t1) ->
               let uu___384_30090 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___384_30090.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___384_30090.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___384_30090.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___384_30090.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____30091 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30093 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____30093 with
           | (univs1,binders,signature) ->
               let uu____30127 =
                 let uu____30132 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30132 with
                 | (univs_opening,univs2) ->
                     let uu____30155 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30155)
                  in
               (match uu____30127 with
                | (univs_opening,univs_closing) ->
                    let uu____30158 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30164 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30165 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30164, uu____30165)  in
                    (match uu____30158 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30189 =
                           match uu____30189 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30207 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30207 with
                                | (us1,t1) ->
                                    let uu____30218 =
                                      let uu____30227 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30238 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30227, uu____30238)  in
                                    (match uu____30218 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30267 =
                                           let uu____30276 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____30287 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____30276, uu____30287)  in
                                         (match uu____30267 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30317 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30317
                                                 in
                                              let uu____30318 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30318 with
                                               | (uu____30341,uu____30342,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30361 =
                                                       let uu____30362 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30362
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30361
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30371 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30371 with
                           | (uu____30388,uu____30389,t1) -> t1  in
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
                             | uu____30459 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30484 =
                               let uu____30485 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30485.FStar_Syntax_Syntax.n  in
                             match uu____30484 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30544 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30575 =
                               let uu____30576 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30576.FStar_Syntax_Syntax.n  in
                             match uu____30575 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30597) ->
                                 let uu____30618 = destruct_action_body body
                                    in
                                 (match uu____30618 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30663 ->
                                 let uu____30664 = destruct_action_body t  in
                                 (match uu____30664 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30713 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30713 with
                           | (action_univs,t) ->
                               let uu____30722 = destruct_action_typ_templ t
                                  in
                               (match uu____30722 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___385_30763 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___385_30763.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___385_30763.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___386_30765 = ed  in
                           let uu____30766 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30767 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30768 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30769 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30770 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30771 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30772 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____30773 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____30774 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____30775 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30776 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____30777 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30778 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30779 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___386_30765.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___386_30765.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____30766;
                             FStar_Syntax_Syntax.bind_wp = uu____30767;
                             FStar_Syntax_Syntax.if_then_else = uu____30768;
                             FStar_Syntax_Syntax.ite_wp = uu____30769;
                             FStar_Syntax_Syntax.stronger = uu____30770;
                             FStar_Syntax_Syntax.close_wp = uu____30771;
                             FStar_Syntax_Syntax.assert_p = uu____30772;
                             FStar_Syntax_Syntax.assume_p = uu____30773;
                             FStar_Syntax_Syntax.null_wp = uu____30774;
                             FStar_Syntax_Syntax.trivial = uu____30775;
                             FStar_Syntax_Syntax.repr = uu____30776;
                             FStar_Syntax_Syntax.return_repr = uu____30777;
                             FStar_Syntax_Syntax.bind_repr = uu____30778;
                             FStar_Syntax_Syntax.actions = uu____30779;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___386_30765.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___387_30782 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___387_30782.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___387_30782.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___387_30782.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___387_30782.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___258_30803 =
            match uu___258_30803 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30834 = elim_uvars_aux_t env us [] t  in
                (match uu____30834 with
                 | (us1,uu____30862,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___388_30889 = sub_eff  in
            let uu____30890 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30893 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___388_30889.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___388_30889.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30890;
              FStar_Syntax_Syntax.lift = uu____30893
            }  in
          let uu___389_30896 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___389_30896.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___389_30896.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___389_30896.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___389_30896.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____30906 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30906 with
           | (univ_names1,binders1,comp1) ->
               let uu___390_30940 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___390_30940.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___390_30940.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___390_30940.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___390_30940.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30943 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30944 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  