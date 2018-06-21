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
    match uu____2985 with | (hd1,uu____3001) -> hd1
  
let mk :
  'Auu____3028 .
    'Auu____3028 ->
      FStar_Range.range -> 'Auu____3028 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3091 = FStar_ST.op_Bang r  in
          match uu____3091 with
          | FStar_Pervasives_Native.Some uu____3143 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3219 =
      FStar_List.map
        (fun uu____3233  ->
           match uu____3233 with
           | (bopt,c) ->
               let uu____3246 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3248 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3246 uu____3248) env
       in
    FStar_All.pipe_right uu____3219 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___241_3251  ->
    match uu___241_3251 with
    | Clos (env,t,uu____3254,uu____3255) ->
        let uu____3300 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3307 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3300 uu____3307
    | Univ uu____3308 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___242_3313  ->
    match uu___242_3313 with
    | Arg (c,uu____3315,uu____3316) ->
        let uu____3317 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3317
    | MemoLazy uu____3318 -> "MemoLazy"
    | Abs (uu____3325,bs,uu____3327,uu____3328,uu____3329) ->
        let uu____3334 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3334
    | UnivArgs uu____3341 -> "UnivArgs"
    | Match uu____3348 -> "Match"
    | App (uu____3357,t,uu____3359,uu____3360) ->
        let uu____3361 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3361
    | Meta (uu____3362,m,uu____3364) -> "Meta"
    | Let uu____3365 -> "Let"
    | Cfg uu____3374 -> "Cfg"
    | Debug (t,uu____3376) ->
        let uu____3377 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3377
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3387 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3387 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let is_empty : 'Auu____3444 . 'Auu____3444 Prims.list -> Prims.bool =
  fun uu___243_3451  ->
    match uu___243_3451 with | [] -> true | uu____3454 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3486 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3486
      with
      | uu____3505 ->
          let uu____3506 =
            let uu____3507 = FStar_Syntax_Print.db_to_string x  in
            let uu____3508 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3507
              uu____3508
             in
          failwith uu____3506
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3516 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3516
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3520 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3520
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3524 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3524
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
          let uu____3558 =
            FStar_List.fold_left
              (fun uu____3584  ->
                 fun u1  ->
                   match uu____3584 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3609 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3609 with
                        | (k_u,n1) ->
                            let uu____3624 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3624
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3558 with
          | (uu____3642,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3669 =
                   let uu____3670 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3670  in
                 match uu____3669 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3688 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3696 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3702 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3711 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3720 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3727 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3727 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3744 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3744 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3752 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3760 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3760 with
                                  | (uu____3765,m) -> n1 <= m))
                           in
                        if uu____3752 then rest1 else us1
                    | uu____3770 -> us1)
               | uu____3775 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3779 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3779
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3783 = aux u  in
           match uu____3783 with
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
            (fun uu____3935  ->
               let uu____3936 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3937 = env_to_string env  in
               let uu____3938 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3936 uu____3937 uu____3938);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3947 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3950 ->
                    let uu____3973 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3973
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3974 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3975 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3976 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3977 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____4001 ->
                           let uu____4014 =
                             let uu____4015 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4016 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4015 uu____4016
                              in
                           failwith uu____4014
                       | uu____4019 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___244_4054  ->
                                         match uu___244_4054 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4061 =
                                               let uu____4068 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4068)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4061
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___288_4078 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___288_4078.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___288_4078.FStar_Syntax_Syntax.sort)
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
                                              | uu____4083 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4086 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___289_4090 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___289_4090.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___289_4090.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4111 =
                        let uu____4112 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4112  in
                      mk uu____4111 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4120 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4120  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4122 = lookup_bvar env x  in
                    (match uu____4122 with
                     | Univ uu____4125 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___290_4129 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___290_4129.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___290_4129.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4135,uu____4136) ->
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
                    let uu____4465 = close_binders cfg env bs  in
                    (match uu____4465 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4520 =
                      let uu____4533 =
                        let uu____4542 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4542]  in
                      close_binders cfg env uu____4533  in
                    (match uu____4520 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4587 =
                             let uu____4588 =
                               let uu____4595 =
                                 let uu____4596 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4596
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4595, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4588  in
                           mk uu____4587 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4695 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4695
                      | FStar_Util.Inr c ->
                          let uu____4709 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4709
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4728 =
                        let uu____4729 =
                          let uu____4756 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4756, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4729  in
                      mk uu____4728 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4802 =
                            let uu____4803 =
                              let uu____4810 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4810, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4803  in
                          mk uu____4802 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4862  -> dummy :: env1) env
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
                    let uu____4883 =
                      let uu____4894 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4894
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4913 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___291_4929 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___291_4929.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___291_4929.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4913))
                       in
                    (match uu____4883 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___292_4947 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___292_4947.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___292_4947.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___292_4947.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___292_4947.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4961,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____5024  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____5041 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5041
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5053  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5077 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5077
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___293_5085 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___293_5085.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___293_5085.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___294_5086 = lb  in
                      let uu____5087 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___294_5086.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___294_5086.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5087;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___294_5086.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___294_5086.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5119  -> fun env1  -> dummy :: env1)
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
            (fun uu____5208  ->
               let uu____5209 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5210 = env_to_string env  in
               let uu____5211 = stack_to_string stack  in
               let uu____5212 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5209 uu____5210 uu____5211 uu____5212);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5217,uu____5218),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5297 = close_binders cfg env' bs  in
               (match uu____5297 with
                | (bs1,uu____5313) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5333 =
                      let uu___295_5336 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___295_5336.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___295_5336.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5333)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5392 =
                 match uu____5392 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5507 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5536 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5620  ->
                                     fun uu____5621  ->
                                       match (uu____5620, uu____5621) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5760 = norm_pat env4 p1
                                              in
                                           (match uu____5760 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5536 with
                            | (pats1,env4) ->
                                ((let uu___296_5922 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___296_5922.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___297_5941 = x  in
                             let uu____5942 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___297_5941.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___297_5941.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5942
                             }  in
                           ((let uu___298_5956 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___298_5956.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___299_5967 = x  in
                             let uu____5968 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___299_5967.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___299_5967.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5968
                             }  in
                           ((let uu___300_5982 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___300_5982.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___301_5998 = x  in
                             let uu____5999 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___301_5998.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___301_5998.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5999
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___302_6016 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___302_6016.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____6021 = norm_pat env2 pat  in
                     (match uu____6021 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6090 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6090
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6109 =
                   let uu____6110 =
                     let uu____6133 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6133)  in
                   FStar_Syntax_Syntax.Tm_match uu____6110  in
                 mk uu____6109 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6248 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6357  ->
                                       match uu____6357 with
                                       | (a,q) ->
                                           let uu____6384 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6384, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6248
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6397 =
                       let uu____6404 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6404)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6397
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6416 =
                       let uu____6425 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6425)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6416
                 | uu____6430 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6436 -> failwith "Impossible: unexpected stack element")

and (close_binders :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____6452 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6535  ->
                  fun uu____6536  ->
                    match (uu____6535, uu____6536) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___303_6676 = b  in
                          let uu____6677 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___303_6676.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___303_6676.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6677
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6452 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6814 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6827 = inline_closure_env cfg env [] t  in
                 let uu____6828 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6827 uu____6828
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6841 = inline_closure_env cfg env [] t  in
                 let uu____6842 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6841 uu____6842
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6896  ->
                           match uu____6896 with
                           | (a,q) ->
                               let uu____6917 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6917, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___245_6934  ->
                           match uu___245_6934 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6938 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6938
                           | f -> f))
                    in
                 let uu____6942 =
                   let uu___304_6943 = c1  in
                   let uu____6944 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6944;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___304_6943.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6942)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___246_6954  ->
            match uu___246_6954 with
            | FStar_Syntax_Syntax.DECREASES uu____6955 -> false
            | uu____6958 -> true))

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
                   (fun uu___247_6976  ->
                      match uu___247_6976 with
                      | FStar_Syntax_Syntax.DECREASES uu____6977 -> false
                      | uu____6980 -> true))
               in
            let rc1 =
              let uu___305_6982 = rc  in
              let uu____6983 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___305_6982.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6983;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6992 -> lopt

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
    let uu____7109 =
      let uu____7118 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____7118  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____7109  in
  let arg_as_bounded_int uu____7148 =
    match uu____7148 with
    | (a,uu____7162) ->
        let uu____7173 =
          let uu____7174 = FStar_Syntax_Subst.compress a  in
          uu____7174.FStar_Syntax_Syntax.n  in
        (match uu____7173 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____7184;
                FStar_Syntax_Syntax.vars = uu____7185;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____7187;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____7188;_},uu____7189)::[])
             when
             let uu____7238 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7238 "int_to_t" ->
             let uu____7239 =
               let uu____7244 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7244)  in
             FStar_Pervasives_Native.Some uu____7239
         | uu____7249 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7297 = f a  in FStar_Pervasives_Native.Some uu____7297
    | uu____7298 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7354 = f a0 a1  in FStar_Pervasives_Native.Some uu____7354
    | uu____7355 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7413 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7413  in
  let binary_op as_a f res args =
    let uu____7486 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7486  in
  let as_primitive_step is_strong uu____7525 =
    match uu____7525 with
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
           let uu____7585 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7585)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7621 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7621)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7650 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7650)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7686 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7686)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7722 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7722)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7864 =
          let uu____7873 = as_a a  in
          let uu____7876 = as_b b  in (uu____7873, uu____7876)  in
        (match uu____7864 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7891 =
               let uu____7892 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7892  in
             FStar_Pervasives_Native.Some uu____7891
         | uu____7893 -> FStar_Pervasives_Native.None)
    | uu____7902 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7922 =
        let uu____7923 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7923  in
      mk uu____7922 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7937 =
      let uu____7940 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7940  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7937  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7982 =
      let uu____7983 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7983  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7982
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____8061 = arg_as_string a1  in
        (match uu____8061 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8067 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____8067 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8080 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____8080
              | uu____8081 -> FStar_Pervasives_Native.None)
         | uu____8086 -> FStar_Pervasives_Native.None)
    | uu____8089 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____8111 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____8111
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8148 =
          let uu____8169 = arg_as_string fn  in
          let uu____8172 = arg_as_int from_line  in
          let uu____8175 = arg_as_int from_col  in
          let uu____8178 = arg_as_int to_line  in
          let uu____8181 = arg_as_int to_col  in
          (uu____8169, uu____8172, uu____8175, uu____8178, uu____8181)  in
        (match uu____8148 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8212 =
                 let uu____8213 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8214 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8213 uu____8214  in
               let uu____8215 =
                 let uu____8216 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8217 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8216 uu____8217  in
               FStar_Range.mk_range fn1 uu____8212 uu____8215  in
             let uu____8218 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8218
         | uu____8219 -> FStar_Pervasives_Native.None)
    | uu____8240 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8273)::(a1,uu____8275)::(a2,uu____8277)::[] ->
        let uu____8334 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8334 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8339 -> FStar_Pervasives_Native.None)
    | uu____8340 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8375)::[] ->
        let uu____8392 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8392 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8398 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8398
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8399 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8427 =
      let uu____8444 =
        let uu____8461 =
          let uu____8478 =
            let uu____8495 =
              let uu____8512 =
                let uu____8529 =
                  let uu____8546 =
                    let uu____8563 =
                      let uu____8580 =
                        let uu____8597 =
                          let uu____8614 =
                            let uu____8631 =
                              let uu____8648 =
                                let uu____8665 =
                                  let uu____8682 =
                                    let uu____8699 =
                                      let uu____8716 =
                                        let uu____8733 =
                                          let uu____8750 =
                                            let uu____8767 =
                                              let uu____8784 =
                                                let uu____8799 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8799,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8808 =
                                                let uu____8825 =
                                                  let uu____8840 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8840,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8853 =
                                                  let uu____8870 =
                                                    let uu____8885 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8885,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8894 =
                                                    let uu____8911 =
                                                      let uu____8926 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8926,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8911]  in
                                                  uu____8870 :: uu____8894
                                                   in
                                                uu____8825 :: uu____8853  in
                                              uu____8784 :: uu____8808  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8767
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8750
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8733
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8716
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8699
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____9146 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____9146 y)))
                                    :: uu____8682
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8665
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8648
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8631
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8614
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8597
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8580
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9341 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9341)))
                      :: uu____8563
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9371 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9371)))
                    :: uu____8546
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9401 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9401)))
                  :: uu____8529
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9431 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9431)))
                :: uu____8512
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8495
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8478
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8461
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8444
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8427
     in
  let weak_ops =
    let uu____9586 =
      let uu____9601 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9601, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9586]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9681 =
        let uu____9686 =
          let uu____9687 = FStar_Syntax_Syntax.as_arg c  in [uu____9687]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9686  in
      uu____9681 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9767 =
                let uu____9782 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9782, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9804  ->
                          fun uu____9805  ->
                            match (uu____9804, uu____9805) with
                            | ((int_to_t1,x),(uu____9824,y)) ->
                                let uu____9834 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9834)))
                 in
              let uu____9835 =
                let uu____9852 =
                  let uu____9867 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9867, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9889  ->
                            fun uu____9890  ->
                              match (uu____9889, uu____9890) with
                              | ((int_to_t1,x),(uu____9909,y)) ->
                                  let uu____9919 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9919)))
                   in
                let uu____9920 =
                  let uu____9937 =
                    let uu____9952 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9952, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9974  ->
                              fun uu____9975  ->
                                match (uu____9974, uu____9975) with
                                | ((int_to_t1,x),(uu____9994,y)) ->
                                    let uu____10004 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____10004)))
                     in
                  let uu____10005 =
                    let uu____10022 =
                      let uu____10037 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____10037, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____10055  ->
                                match uu____10055 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____10022]  in
                  uu____9937 :: uu____10005  in
                uu____9852 :: uu____9920  in
              uu____9767 :: uu____9835))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10185 =
                let uu____10200 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____10200, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____10222  ->
                          fun uu____10223  ->
                            match (uu____10222, uu____10223) with
                            | ((int_to_t1,x),(uu____10242,y)) ->
                                let uu____10252 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded r int_to_t1 uu____10252)))
                 in
              let uu____10253 =
                let uu____10270 =
                  let uu____10285 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10285, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10307  ->
                            fun uu____10308  ->
                              match (uu____10307, uu____10308) with
                              | ((int_to_t1,x),(uu____10327,y)) ->
                                  let uu____10337 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10337)))
                   in
                [uu____10270]  in
              uu____10185 :: uu____10253))
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
    | (_typ,uu____10467)::(a1,uu____10469)::(a2,uu____10471)::[] ->
        let uu____10528 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10528 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10532 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10532.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10532.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___307_10534 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___307_10534.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___307_10534.FStar_Syntax_Syntax.vars)
                })
         | uu____10535 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10537)::uu____10538::(a1,uu____10540)::(a2,uu____10542)::[]
        ->
        let uu____10615 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10615 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___306_10619 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___306_10619.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___306_10619.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___307_10621 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___307_10621.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___307_10621.FStar_Syntax_Syntax.vars)
                })
         | uu____10622 -> FStar_Pervasives_Native.None)
    | uu____10623 -> failwith "Unexpected number of arguments"  in
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
    let uu____10677 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10677 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10729 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10729) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10791  ->
           fun subst1  ->
             match uu____10791 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10832,uu____10833)) ->
                      let uu____10892 = b  in
                      (match uu____10892 with
                       | (bv,uu____10900) ->
                           let uu____10901 =
                             let uu____10902 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10902  in
                           if uu____10901
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10907 = unembed_binder term1  in
                              match uu____10907 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10914 =
                                      let uu___308_10915 = bv  in
                                      let uu____10916 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___308_10915.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___308_10915.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10916
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10914
                                     in
                                  let b_for_x =
                                    let uu____10922 =
                                      let uu____10929 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10929)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10922  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___248_10945  ->
                                         match uu___248_10945 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10946,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10948;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10949;_})
                                             ->
                                             let uu____10954 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10954
                                         | uu____10955 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10956 -> subst1)) env []
  
let reduce_primops :
  'Auu____10979 'Auu____10980 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10979) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10980 ->
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
            (let uu____11028 = FStar_Syntax_Util.head_and_args tm  in
             match uu____11028 with
             | (head1,args) ->
                 let uu____11073 =
                   let uu____11074 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11074.FStar_Syntax_Syntax.n  in
                 (match uu____11073 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____11080 = find_prim_step cfg fv  in
                      (match uu____11080 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____11108  ->
                                   let uu____11109 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____11110 =
                                     FStar_Util.string_of_int l  in
                                   let uu____11117 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____11109 uu____11110 uu____11117);
                              tm)
                           else
                             (let uu____11119 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____11119 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____11256  ->
                                        let uu____11257 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____11257);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____11260  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____11262 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____11262 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____11270  ->
                                              let uu____11271 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____11271);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____11277  ->
                                              let uu____11278 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____11279 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____11278 uu____11279);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____11280 ->
                           (log_primops cfg
                              (fun uu____11284  ->
                                 let uu____11285 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____11285);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11289  ->
                            let uu____11290 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11290);
                       (match args with
                        | (a1,uu____11294)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____11319 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11333  ->
                            let uu____11334 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11334);
                       (match args with
                        | (t,uu____11338)::(r,uu____11340)::[] ->
                            let uu____11381 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11381 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11387 -> tm))
                  | uu____11398 -> tm))
  
let reduce_equality :
  'Auu____11409 'Auu____11410 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11409) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11410 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___309_11456 = cfg  in
         {
           steps =
             (let uu___310_11459 = default_steps  in
              {
                beta = (uu___310_11459.beta);
                iota = (uu___310_11459.iota);
                zeta = (uu___310_11459.zeta);
                weak = (uu___310_11459.weak);
                hnf = (uu___310_11459.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___310_11459.do_not_unfold_pure_lets);
                unfold_until = (uu___310_11459.unfold_until);
                unfold_only = (uu___310_11459.unfold_only);
                unfold_fully = (uu___310_11459.unfold_fully);
                unfold_attr = (uu___310_11459.unfold_attr);
                unfold_tac = (uu___310_11459.unfold_tac);
                pure_subterms_within_computations =
                  (uu___310_11459.pure_subterms_within_computations);
                simplify = (uu___310_11459.simplify);
                erase_universes = (uu___310_11459.erase_universes);
                allow_unbound_universes =
                  (uu___310_11459.allow_unbound_universes);
                reify_ = (uu___310_11459.reify_);
                compress_uvars = (uu___310_11459.compress_uvars);
                no_full_norm = (uu___310_11459.no_full_norm);
                check_no_uvars = (uu___310_11459.check_no_uvars);
                unmeta = (uu___310_11459.unmeta);
                unascribe = (uu___310_11459.unascribe);
                in_full_norm_request = (uu___310_11459.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___310_11459.weakly_reduce_scrutinee)
              });
           tcenv = (uu___309_11456.tcenv);
           debug = (uu___309_11456.debug);
           delta_level = (uu___309_11456.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___309_11456.strong);
           memoize_lazy = (uu___309_11456.memoize_lazy);
           normalize_pure_lets = (uu___309_11456.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11466 .
    FStar_Syntax_Syntax.term -> 'Auu____11466 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11481 =
        let uu____11488 =
          let uu____11489 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11489.FStar_Syntax_Syntax.n  in
        (uu____11488, args)  in
      match uu____11481 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11495::uu____11496::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11500::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11505::uu____11506::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11509 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___249_11522  ->
    match uu___249_11522 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11528 =
          let uu____11531 =
            let uu____11532 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11532  in
          [uu____11531]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11528
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11538 =
          let uu____11541 =
            let uu____11542 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11542  in
          [uu____11541]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11538
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11565 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11565)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11616 =
            let uu____11621 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11621 s  in
          match uu____11616 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11637 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11637
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11663::(tm,uu____11665)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11694)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11715)::uu____11716::(tm,uu____11718)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11759 =
              let uu____11764 = full_norm steps  in parse_steps uu____11764
               in
            (match uu____11759 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11803 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___250_11822  ->
    match uu___250_11822 with
    | (App
        (uu____11825,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11826;
                       FStar_Syntax_Syntax.vars = uu____11827;_},uu____11828,uu____11829))::uu____11830
        -> true
    | uu____11835 -> false
  
let firstn :
  'Auu____11844 .
    Prims.int ->
      'Auu____11844 Prims.list ->
        ('Auu____11844 Prims.list,'Auu____11844 Prims.list)
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
          (uu____11886,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11887;
                         FStar_Syntax_Syntax.vars = uu____11888;_},uu____11889,uu____11890))::uu____11891
          -> (cfg.steps).reify_
      | uu____11896 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11919) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11929) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11950  ->
                  match uu____11950 with
                  | (a,uu____11960) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11970 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11993 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11994 -> false
    | FStar_Syntax_Syntax.Tm_type uu____12007 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____12008 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____12009 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____12010 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____12011 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____12012 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____12019 -> false
    | FStar_Syntax_Syntax.Tm_let uu____12026 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____12039 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____12058 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____12073 -> true
    | FStar_Syntax_Syntax.Tm_match uu____12080 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____12150  ->
                   match uu____12150 with
                   | (a,uu____12160) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12171) ->
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
                     (fun uu____12299  ->
                        match uu____12299 with
                        | (a,uu____12309) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____12318,uu____12319,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____12325,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____12331 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____12338 -> false
            | FStar_Syntax_Syntax.Meta_named uu____12339 -> false))
  
let decide_unfolding :
  'Auu____12354 .
    cfg ->
      'Auu____12354 Prims.list ->
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
                (fun uu____12446  ->
                   let uu____12447 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____12448 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____12449 =
                     let uu____12450 =
                       let uu____12453 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____12453
                        in
                     stack_to_string uu____12450  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____12447 uu____12448 uu____12449);
              (let attrs =
                 let uu____12479 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____12479 with
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
                   (fun uu____12607  ->
                      fun uu____12608  ->
                        match (uu____12607, uu____12608) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____12668 =
                 match uu____12668 with
                 | (x,y,z) ->
                     let uu____12678 = FStar_Util.string_of_bool x  in
                     let uu____12679 = FStar_Util.string_of_bool y  in
                     let uu____12680 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____12678 uu____12679
                       uu____12680
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____12726 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____12772  ->
                           let uu____12773 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____12774 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____12773 uu____12774);
                      if b then reif else no)
                 | uu____12782 when
                     let uu____12823 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____12823 -> no
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____12827),uu____12828);
                        FStar_Syntax_Syntax.sigrng = uu____12829;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____12831;
                        FStar_Syntax_Syntax.sigattrs = uu____12832;_},uu____12833),uu____12834),uu____12835,uu____12836,uu____12837)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     -> no
                 | (uu____12940,uu____12941,uu____12942,uu____12943) when
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
                          ((is_rec,uu____13009),uu____13010);
                        FStar_Syntax_Syntax.sigrng = uu____13011;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____13013;
                        FStar_Syntax_Syntax.sigattrs = uu____13014;_},uu____13015),uu____13016),uu____13017,uu____13018,uu____13019)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     no
                 | (uu____13122,FStar_Pervasives_Native.Some
                    uu____13123,uu____13124,uu____13125) ->
                     (log_unfolding cfg
                        (fun uu____13193  ->
                           let uu____13194 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13194);
                      (let uu____13195 =
                         let uu____13204 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13224 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13224
                            in
                         let uu____13231 =
                           let uu____13240 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13260 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13260
                              in
                           let uu____13269 =
                             let uu____13278 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13298 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13298
                                in
                             [uu____13278]  in
                           uu____13240 :: uu____13269  in
                         uu____13204 :: uu____13231  in
                       comb_or uu____13195))
                 | (uu____13329,uu____13330,FStar_Pervasives_Native.Some
                    uu____13331,uu____13332) ->
                     (log_unfolding cfg
                        (fun uu____13400  ->
                           let uu____13401 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13401);
                      (let uu____13402 =
                         let uu____13411 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13431 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13431
                            in
                         let uu____13438 =
                           let uu____13447 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13467 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13467
                              in
                           let uu____13476 =
                             let uu____13485 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13505 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13505
                                in
                             [uu____13485]  in
                           uu____13447 :: uu____13476  in
                         uu____13411 :: uu____13438  in
                       comb_or uu____13402))
                 | (uu____13536,uu____13537,uu____13538,FStar_Pervasives_Native.Some
                    uu____13539) ->
                     (log_unfolding cfg
                        (fun uu____13607  ->
                           let uu____13608 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13608);
                      (let uu____13609 =
                         let uu____13618 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13638 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13638
                            in
                         let uu____13645 =
                           let uu____13654 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13674 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13674
                              in
                           let uu____13683 =
                             let uu____13692 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13712 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13712
                                in
                             [uu____13692]  in
                           uu____13654 :: uu____13683  in
                         uu____13618 :: uu____13645  in
                       comb_or uu____13609))
                 | uu____13743 ->
                     (log_unfolding cfg
                        (fun uu____13789  ->
                           let uu____13790 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____13791 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____13792 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____13790 uu____13791 uu____13792);
                      (let uu____13793 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___251_13797  ->
                                 match uu___251_13797 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____13793))
                  in
               log_unfolding cfg
                 (fun uu____13810  ->
                    let uu____13811 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____13812 = FStar_Range.string_of_range rng  in
                    let uu____13813 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____13811 uu____13812 uu____13813);
               (match res with
                | (false ,uu____13822,uu____13823) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___311_13839 = cfg  in
                      {
                        steps =
                          (let uu___312_13842 = cfg.steps  in
                           {
                             beta = (uu___312_13842.beta);
                             iota = (uu___312_13842.iota);
                             zeta = (uu___312_13842.zeta);
                             weak = (uu___312_13842.weak);
                             hnf = (uu___312_13842.hnf);
                             primops = (uu___312_13842.primops);
                             do_not_unfold_pure_lets =
                               (uu___312_13842.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___312_13842.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___312_13842.pure_subterms_within_computations);
                             simplify = (uu___312_13842.simplify);
                             erase_universes =
                               (uu___312_13842.erase_universes);
                             allow_unbound_universes =
                               (uu___312_13842.allow_unbound_universes);
                             reify_ = (uu___312_13842.reify_);
                             compress_uvars = (uu___312_13842.compress_uvars);
                             no_full_norm = (uu___312_13842.no_full_norm);
                             check_no_uvars = (uu___312_13842.check_no_uvars);
                             unmeta = (uu___312_13842.unmeta);
                             unascribe = (uu___312_13842.unascribe);
                             in_full_norm_request =
                               (uu___312_13842.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___312_13842.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___311_13839.tcenv);
                        debug = (uu___311_13839.debug);
                        delta_level = (uu___311_13839.delta_level);
                        primitive_steps = (uu___311_13839.primitive_steps);
                        strong = (uu___311_13839.strong);
                        memoize_lazy = (uu___311_13839.memoize_lazy);
                        normalize_pure_lets =
                          (uu___311_13839.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____13860 =
                      let uu____13867 = FStar_List.tl stack  in
                      (cfg, uu____13867)  in
                    FStar_Pervasives_Native.Some uu____13860
                | uu____13878 ->
                    let uu____13885 =
                      let uu____13886 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____13886
                       in
                    FStar_All.pipe_left failwith uu____13885))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____14202 ->
                   let uu____14225 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____14225
               | uu____14226 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____14234  ->
               let uu____14235 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____14236 = FStar_Syntax_Print.term_to_string t1  in
               let uu____14237 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____14244 =
                 let uu____14245 =
                   let uu____14248 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____14248
                    in
                 stack_to_string uu____14245  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____14235 uu____14236 uu____14237 uu____14244);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____14274  ->
                     let uu____14275 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14275);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____14276 ->
               (log_unfolding cfg
                  (fun uu____14280  ->
                     let uu____14281 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14281);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____14282 ->
               (log_unfolding cfg
                  (fun uu____14286  ->
                     let uu____14287 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14287);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____14288 ->
               (log_unfolding cfg
                  (fun uu____14292  ->
                     let uu____14293 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14293);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14294;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____14295;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____14301  ->
                     let uu____14302 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14302);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14303;
                 FStar_Syntax_Syntax.fv_delta = uu____14304;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____14308  ->
                     let uu____14309 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14309);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14310;
                 FStar_Syntax_Syntax.fv_delta = uu____14311;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____14312);_}
               ->
               (log_unfolding cfg
                  (fun uu____14322  ->
                     let uu____14323 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14323);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14326 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14326  in
               let uu____14327 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14327 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____14360 ->
               let uu____14367 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14367
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____14403 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____14403)
               ->
               let cfg' =
                 let uu___313_14405 = cfg  in
                 {
                   steps =
                     (let uu___314_14408 = cfg.steps  in
                      {
                        beta = (uu___314_14408.beta);
                        iota = (uu___314_14408.iota);
                        zeta = (uu___314_14408.zeta);
                        weak = (uu___314_14408.weak);
                        hnf = (uu___314_14408.hnf);
                        primops = (uu___314_14408.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___314_14408.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___314_14408.unfold_attr);
                        unfold_tac = (uu___314_14408.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___314_14408.pure_subterms_within_computations);
                        simplify = (uu___314_14408.simplify);
                        erase_universes = (uu___314_14408.erase_universes);
                        allow_unbound_universes =
                          (uu___314_14408.allow_unbound_universes);
                        reify_ = (uu___314_14408.reify_);
                        compress_uvars = (uu___314_14408.compress_uvars);
                        no_full_norm = (uu___314_14408.no_full_norm);
                        check_no_uvars = (uu___314_14408.check_no_uvars);
                        unmeta = (uu___314_14408.unmeta);
                        unascribe = (uu___314_14408.unascribe);
                        in_full_norm_request =
                          (uu___314_14408.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___314_14408.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___313_14405.tcenv);
                   debug = (uu___313_14405.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___313_14405.primitive_steps);
                   strong = (uu___313_14405.strong);
                   memoize_lazy = (uu___313_14405.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____14413 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____14413 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14444  ->
                              fun stack1  ->
                                match uu____14444 with
                                | (a,aq) ->
                                    let uu____14456 =
                                      let uu____14457 =
                                        let uu____14464 =
                                          let uu____14465 =
                                            let uu____14496 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14496, false)  in
                                          Clos uu____14465  in
                                        (uu____14464, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14457  in
                                    uu____14456 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14584  ->
                          let uu____14585 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14585);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14609 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___252_14614  ->
                                match uu___252_14614 with
                                | UnfoldUntil uu____14615 -> true
                                | UnfoldOnly uu____14616 -> true
                                | UnfoldFully uu____14619 -> true
                                | uu____14622 -> false))
                         in
                      if uu____14609
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___315_14627 = cfg  in
                      let uu____14628 =
                        let uu___316_14629 = to_fsteps s  in
                        {
                          beta = (uu___316_14629.beta);
                          iota = (uu___316_14629.iota);
                          zeta = (uu___316_14629.zeta);
                          weak = (uu___316_14629.weak);
                          hnf = (uu___316_14629.hnf);
                          primops = (uu___316_14629.primops);
                          do_not_unfold_pure_lets =
                            (uu___316_14629.do_not_unfold_pure_lets);
                          unfold_until = (uu___316_14629.unfold_until);
                          unfold_only = (uu___316_14629.unfold_only);
                          unfold_fully = (uu___316_14629.unfold_fully);
                          unfold_attr = (uu___316_14629.unfold_attr);
                          unfold_tac = (uu___316_14629.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___316_14629.pure_subterms_within_computations);
                          simplify = (uu___316_14629.simplify);
                          erase_universes = (uu___316_14629.erase_universes);
                          allow_unbound_universes =
                            (uu___316_14629.allow_unbound_universes);
                          reify_ = (uu___316_14629.reify_);
                          compress_uvars = (uu___316_14629.compress_uvars);
                          no_full_norm = (uu___316_14629.no_full_norm);
                          check_no_uvars = (uu___316_14629.check_no_uvars);
                          unmeta = (uu___316_14629.unmeta);
                          unascribe = (uu___316_14629.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___316_14629.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14628;
                        tcenv = (uu___315_14627.tcenv);
                        debug = (uu___315_14627.debug);
                        delta_level;
                        primitive_steps = (uu___315_14627.primitive_steps);
                        strong = (uu___315_14627.strong);
                        memoize_lazy = (uu___315_14627.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14634 =
                          let uu____14635 =
                            let uu____14640 = FStar_Util.now ()  in
                            (t1, uu____14640)  in
                          Debug uu____14635  in
                        uu____14634 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14644 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14644
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14653 =
                      let uu____14660 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14660, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14653  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14669 = lookup_bvar env x  in
               (match uu____14669 with
                | Univ uu____14670 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14719 = FStar_ST.op_Bang r  in
                      (match uu____14719 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14841  ->
                                 let uu____14842 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14843 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14842
                                   uu____14843);
                            (let uu____14844 = maybe_weakly_reduced t'  in
                             if uu____14844
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14845 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14920)::uu____14921 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14931,uu____14932))::stack_rest ->
                    (match c with
                     | Univ uu____14936 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14945 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14974  ->
                                    let uu____14975 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14975);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____15009  ->
                                    let uu____15010 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____15010);
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
                       (fun uu____15078  ->
                          let uu____15079 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____15079);
                     norm cfg env stack1 t1)
                | (Match uu____15080)::uu____15081 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15095 = cfg.steps  in
                             {
                               beta = (uu___317_15095.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15095.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15095.unfold_until);
                               unfold_only = (uu___317_15095.unfold_only);
                               unfold_fully = (uu___317_15095.unfold_fully);
                               unfold_attr = (uu___317_15095.unfold_attr);
                               unfold_tac = (uu___317_15095.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15095.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15095.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15095.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15095.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15095.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15095.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15097 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15097.tcenv);
                               debug = (uu___318_15097.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15097.primitive_steps);
                               strong = (uu___318_15097.strong);
                               memoize_lazy = (uu___318_15097.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15097.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15099 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15099 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15135  -> dummy :: env1) env)
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
                                          let uu____15178 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15178)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15185 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15185.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15185.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15186 -> lopt  in
                           (log cfg
                              (fun uu____15192  ->
                                 let uu____15193 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15193);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15204 = cfg  in
                               {
                                 steps = (uu___320_15204.steps);
                                 tcenv = (uu___320_15204.tcenv);
                                 debug = (uu___320_15204.debug);
                                 delta_level = (uu___320_15204.delta_level);
                                 primitive_steps =
                                   (uu___320_15204.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15204.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15204.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____15207)::uu____15208 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15218 = cfg.steps  in
                             {
                               beta = (uu___317_15218.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15218.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15218.unfold_until);
                               unfold_only = (uu___317_15218.unfold_only);
                               unfold_fully = (uu___317_15218.unfold_fully);
                               unfold_attr = (uu___317_15218.unfold_attr);
                               unfold_tac = (uu___317_15218.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15218.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15218.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15218.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15218.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15218.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15218.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15220 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15220.tcenv);
                               debug = (uu___318_15220.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15220.primitive_steps);
                               strong = (uu___318_15220.strong);
                               memoize_lazy = (uu___318_15220.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15220.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15222 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15222 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15258  -> dummy :: env1) env)
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
                                          let uu____15301 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15301)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15308 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15308.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15308.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15309 -> lopt  in
                           (log cfg
                              (fun uu____15315  ->
                                 let uu____15316 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15316);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15327 = cfg  in
                               {
                                 steps = (uu___320_15327.steps);
                                 tcenv = (uu___320_15327.tcenv);
                                 debug = (uu___320_15327.debug);
                                 delta_level = (uu___320_15327.delta_level);
                                 primitive_steps =
                                   (uu___320_15327.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15327.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15327.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____15330)::uu____15331 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15343 = cfg.steps  in
                             {
                               beta = (uu___317_15343.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15343.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15343.unfold_until);
                               unfold_only = (uu___317_15343.unfold_only);
                               unfold_fully = (uu___317_15343.unfold_fully);
                               unfold_attr = (uu___317_15343.unfold_attr);
                               unfold_tac = (uu___317_15343.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15343.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15343.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15343.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15343.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15343.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15343.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15345 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15345.tcenv);
                               debug = (uu___318_15345.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15345.primitive_steps);
                               strong = (uu___318_15345.strong);
                               memoize_lazy = (uu___318_15345.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15345.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15347 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15347 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15383  -> dummy :: env1) env)
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
                                          let uu____15426 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15426)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15433 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15433.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15433.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15434 -> lopt  in
                           (log cfg
                              (fun uu____15440  ->
                                 let uu____15441 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15441);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15452 = cfg  in
                               {
                                 steps = (uu___320_15452.steps);
                                 tcenv = (uu___320_15452.tcenv);
                                 debug = (uu___320_15452.debug);
                                 delta_level = (uu___320_15452.delta_level);
                                 primitive_steps =
                                   (uu___320_15452.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15452.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15452.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____15455)::uu____15456 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15470 = cfg.steps  in
                             {
                               beta = (uu___317_15470.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15470.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15470.unfold_until);
                               unfold_only = (uu___317_15470.unfold_only);
                               unfold_fully = (uu___317_15470.unfold_fully);
                               unfold_attr = (uu___317_15470.unfold_attr);
                               unfold_tac = (uu___317_15470.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15470.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15470.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15470.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15470.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15470.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15470.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15472 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15472.tcenv);
                               debug = (uu___318_15472.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15472.primitive_steps);
                               strong = (uu___318_15472.strong);
                               memoize_lazy = (uu___318_15472.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15472.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15474 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15474 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15510  -> dummy :: env1) env)
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
                                          let uu____15553 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15553)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15560 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15560.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15560.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15561 -> lopt  in
                           (log cfg
                              (fun uu____15567  ->
                                 let uu____15568 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15568);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15579 = cfg  in
                               {
                                 steps = (uu___320_15579.steps);
                                 tcenv = (uu___320_15579.tcenv);
                                 debug = (uu___320_15579.debug);
                                 delta_level = (uu___320_15579.delta_level);
                                 primitive_steps =
                                   (uu___320_15579.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15579.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15579.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15582)::uu____15583 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15597 = cfg.steps  in
                             {
                               beta = (uu___317_15597.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15597.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15597.unfold_until);
                               unfold_only = (uu___317_15597.unfold_only);
                               unfold_fully = (uu___317_15597.unfold_fully);
                               unfold_attr = (uu___317_15597.unfold_attr);
                               unfold_tac = (uu___317_15597.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15597.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15597.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15597.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15597.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15597.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15597.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15599 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15599.tcenv);
                               debug = (uu___318_15599.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15599.primitive_steps);
                               strong = (uu___318_15599.strong);
                               memoize_lazy = (uu___318_15599.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15599.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15601 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15601 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15637  -> dummy :: env1) env)
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
                                          let uu____15680 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15680)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15687 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15687.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15687.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15688 -> lopt  in
                           (log cfg
                              (fun uu____15694  ->
                                 let uu____15695 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15695);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15706 = cfg  in
                               {
                                 steps = (uu___320_15706.steps);
                                 tcenv = (uu___320_15706.tcenv);
                                 debug = (uu___320_15706.debug);
                                 delta_level = (uu___320_15706.delta_level);
                                 primitive_steps =
                                   (uu___320_15706.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15706.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15706.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15709)::uu____15710 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___317_15728 = cfg.steps  in
                             {
                               beta = (uu___317_15728.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15728.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15728.unfold_until);
                               unfold_only = (uu___317_15728.unfold_only);
                               unfold_fully = (uu___317_15728.unfold_fully);
                               unfold_attr = (uu___317_15728.unfold_attr);
                               unfold_tac = (uu___317_15728.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15728.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15728.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15728.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15728.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15728.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15728.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15730 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15730.tcenv);
                               debug = (uu___318_15730.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15730.primitive_steps);
                               strong = (uu___318_15730.strong);
                               memoize_lazy = (uu___318_15730.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15730.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15732 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15732 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15768  -> dummy :: env1) env)
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
                                          let uu____15811 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15811)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15818 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15818.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15818.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15819 -> lopt  in
                           (log cfg
                              (fun uu____15825  ->
                                 let uu____15826 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15826);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15837 = cfg  in
                               {
                                 steps = (uu___320_15837.steps);
                                 tcenv = (uu___320_15837.tcenv);
                                 debug = (uu___320_15837.debug);
                                 delta_level = (uu___320_15837.delta_level);
                                 primitive_steps =
                                   (uu___320_15837.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15837.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15837.normalize_pure_lets)
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
                             let uu___317_15843 = cfg.steps  in
                             {
                               beta = (uu___317_15843.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___317_15843.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___317_15843.unfold_until);
                               unfold_only = (uu___317_15843.unfold_only);
                               unfold_fully = (uu___317_15843.unfold_fully);
                               unfold_attr = (uu___317_15843.unfold_attr);
                               unfold_tac = (uu___317_15843.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___317_15843.erase_universes);
                               allow_unbound_universes =
                                 (uu___317_15843.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___317_15843.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___317_15843.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___317_15843.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___317_15843.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___318_15845 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___318_15845.tcenv);
                               debug = (uu___318_15845.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___318_15845.primitive_steps);
                               strong = (uu___318_15845.strong);
                               memoize_lazy = (uu___318_15845.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___318_15845.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15847 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15847 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15883  -> dummy :: env1) env)
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
                                          let uu____15926 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15926)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___319_15933 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___319_15933.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___319_15933.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15934 -> lopt  in
                           (log cfg
                              (fun uu____15940  ->
                                 let uu____15941 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15941);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___320_15952 = cfg  in
                               {
                                 steps = (uu___320_15952.steps);
                                 tcenv = (uu___320_15952.tcenv);
                                 debug = (uu___320_15952.debug);
                                 delta_level = (uu___320_15952.delta_level);
                                 primitive_steps =
                                   (uu___320_15952.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___320_15952.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___320_15952.normalize_pure_lets)
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
                      (fun uu____15995  ->
                         fun stack1  ->
                           match uu____15995 with
                           | (a,aq) ->
                               let uu____16007 =
                                 let uu____16008 =
                                   let uu____16015 =
                                     let uu____16016 =
                                       let uu____16047 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____16047, false)  in
                                     Clos uu____16016  in
                                   (uu____16015, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____16008  in
                               uu____16007 :: stack1) args)
                  in
               (log cfg
                  (fun uu____16135  ->
                     let uu____16136 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____16136);
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
                             ((let uu___321_16184 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___321_16184.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___321_16184.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____16185 ->
                      let uu____16200 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____16200)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____16203 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____16203 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____16234 =
                          let uu____16235 =
                            let uu____16242 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___322_16248 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___322_16248.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___322_16248.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____16242)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____16235  in
                        mk uu____16234 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____16271 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____16271
               else
                 (let uu____16273 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____16273 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____16281 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____16307  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____16281 c1  in
                      let t2 =
                        let uu____16331 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____16331 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____16444)::uu____16445 ->
                    (log cfg
                       (fun uu____16458  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____16459)::uu____16460 ->
                    (log cfg
                       (fun uu____16471  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____16472,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____16473;
                                   FStar_Syntax_Syntax.vars = uu____16474;_},uu____16475,uu____16476))::uu____16477
                    ->
                    (log cfg
                       (fun uu____16484  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____16485)::uu____16486 ->
                    (log cfg
                       (fun uu____16497  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____16498 ->
                    (log cfg
                       (fun uu____16501  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____16505  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____16530 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____16530
                         | FStar_Util.Inr c ->
                             let uu____16544 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16544
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16567 =
                               let uu____16568 =
                                 let uu____16595 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16595, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16568
                                in
                             mk uu____16567 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16630 ->
                           let uu____16631 =
                             let uu____16632 =
                               let uu____16633 =
                                 let uu____16660 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16660, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16633
                                in
                             mk uu____16632 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16631))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___323_16737 = cfg  in
                   {
                     steps =
                       (let uu___324_16740 = cfg.steps  in
                        {
                          beta = (uu___324_16740.beta);
                          iota = (uu___324_16740.iota);
                          zeta = (uu___324_16740.zeta);
                          weak = true;
                          hnf = (uu___324_16740.hnf);
                          primops = (uu___324_16740.primops);
                          do_not_unfold_pure_lets =
                            (uu___324_16740.do_not_unfold_pure_lets);
                          unfold_until = (uu___324_16740.unfold_until);
                          unfold_only = (uu___324_16740.unfold_only);
                          unfold_fully = (uu___324_16740.unfold_fully);
                          unfold_attr = (uu___324_16740.unfold_attr);
                          unfold_tac = (uu___324_16740.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___324_16740.pure_subterms_within_computations);
                          simplify = (uu___324_16740.simplify);
                          erase_universes = (uu___324_16740.erase_universes);
                          allow_unbound_universes =
                            (uu___324_16740.allow_unbound_universes);
                          reify_ = (uu___324_16740.reify_);
                          compress_uvars = (uu___324_16740.compress_uvars);
                          no_full_norm = (uu___324_16740.no_full_norm);
                          check_no_uvars = (uu___324_16740.check_no_uvars);
                          unmeta = (uu___324_16740.unmeta);
                          unascribe = (uu___324_16740.unascribe);
                          in_full_norm_request =
                            (uu___324_16740.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___324_16740.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___323_16737.tcenv);
                     debug = (uu___323_16737.debug);
                     delta_level = (uu___323_16737.delta_level);
                     primitive_steps = (uu___323_16737.primitive_steps);
                     strong = (uu___323_16737.strong);
                     memoize_lazy = (uu___323_16737.memoize_lazy);
                     normalize_pure_lets =
                       (uu___323_16737.normalize_pure_lets)
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
                         let uu____16776 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16776 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___325_16796 = cfg  in
                               let uu____16797 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___325_16796.steps);
                                 tcenv = uu____16797;
                                 debug = (uu___325_16796.debug);
                                 delta_level = (uu___325_16796.delta_level);
                                 primitive_steps =
                                   (uu___325_16796.primitive_steps);
                                 strong = (uu___325_16796.strong);
                                 memoize_lazy = (uu___325_16796.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___325_16796.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16804 =
                                 let uu____16805 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16805  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16804
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___326_16808 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___326_16808.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___326_16808.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___326_16808.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___326_16808.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16809 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16809
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16820,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16821;
                               FStar_Syntax_Syntax.lbunivs = uu____16822;
                               FStar_Syntax_Syntax.lbtyp = uu____16823;
                               FStar_Syntax_Syntax.lbeff = uu____16824;
                               FStar_Syntax_Syntax.lbdef = uu____16825;
                               FStar_Syntax_Syntax.lbattrs = uu____16826;
                               FStar_Syntax_Syntax.lbpos = uu____16827;_}::uu____16828),uu____16829)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16869 =
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
               if uu____16869
               then
                 let binder =
                   let uu____16871 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16871  in
                 let env1 =
                   let uu____16881 =
                     let uu____16888 =
                       let uu____16889 =
                         let uu____16920 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16920,
                           false)
                          in
                       Clos uu____16889  in
                     ((FStar_Pervasives_Native.Some binder), uu____16888)  in
                   uu____16881 :: env  in
                 (log cfg
                    (fun uu____17015  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____17019  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____17020 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____17020))
                 else
                   (let uu____17022 =
                      let uu____17027 =
                        let uu____17028 =
                          let uu____17035 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____17035
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____17028]  in
                      FStar_Syntax_Subst.open_term uu____17027 body  in
                    match uu____17022 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____17062  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____17070 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____17070  in
                            FStar_Util.Inl
                              (let uu___327_17086 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___327_17086.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___327_17086.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____17089  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___328_17091 = lb  in
                             let uu____17092 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___328_17091.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___328_17091.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17092;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___328_17091.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___328_17091.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____17121  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___329_17146 = cfg  in
                             {
                               steps = (uu___329_17146.steps);
                               tcenv = (uu___329_17146.tcenv);
                               debug = (uu___329_17146.debug);
                               delta_level = (uu___329_17146.delta_level);
                               primitive_steps =
                                 (uu___329_17146.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___329_17146.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___329_17146.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____17149  ->
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
               let uu____17166 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____17166 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____17202 =
                               let uu___330_17203 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___330_17203.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___330_17203.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____17202  in
                           let uu____17204 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____17204 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____17230 =
                                   FStar_List.map (fun uu____17246  -> dummy)
                                     lbs1
                                    in
                                 let uu____17247 =
                                   let uu____17256 =
                                     FStar_List.map
                                       (fun uu____17278  -> dummy) xs1
                                      in
                                   FStar_List.append uu____17256 env  in
                                 FStar_List.append uu____17230 uu____17247
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____17304 =
                                       let uu___331_17305 = rc  in
                                       let uu____17306 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___331_17305.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____17306;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___331_17305.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____17304
                                 | uu____17315 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___332_17321 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___332_17321.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___332_17321.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___332_17321.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___332_17321.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____17331 =
                        FStar_List.map (fun uu____17347  -> dummy) lbs2  in
                      FStar_List.append uu____17331 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____17355 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____17355 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___333_17371 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___333_17371.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___333_17371.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____17400 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____17400
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____17419 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____17495  ->
                        match uu____17495 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___334_17616 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___334_17616.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___334_17616.FStar_Syntax_Syntax.sort)
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
               (match uu____17419 with
                | (rec_env,memos,uu____17843) ->
                    let uu____17896 =
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
                             let uu____18219 =
                               let uu____18226 =
                                 let uu____18227 =
                                   let uu____18258 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____18258, false)
                                    in
                                 Clos uu____18227  in
                               (FStar_Pervasives_Native.None, uu____18226)
                                in
                             uu____18219 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____18362  ->
                     let uu____18363 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____18363);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____18385 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____18387::uu____18388 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____18393) ->
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
                             | uu____18420 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____18436 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____18436
                              | uu____18449 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____18455 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____18479 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____18493 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____18506 =
                        let uu____18507 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____18508 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____18507 uu____18508
                         in
                      failwith uu____18506
                    else
                      (let uu____18510 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____18510)
                | uu____18511 -> norm cfg env stack t2))

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
              let uu____18520 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____18520 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____18534  ->
                        let uu____18535 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____18535);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____18546  ->
                        let uu____18547 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____18548 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____18547 uu____18548);
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
                      | (UnivArgs (us',uu____18561))::stack1 ->
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
                      | uu____18600 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____18603 ->
                          let uu____18606 =
                            let uu____18607 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____18607
                             in
                          failwith uu____18606
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
                  let uu___335_18631 = cfg  in
                  let uu____18632 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18632;
                    tcenv = (uu___335_18631.tcenv);
                    debug = (uu___335_18631.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___335_18631.primitive_steps);
                    strong = (uu___335_18631.strong);
                    memoize_lazy = (uu___335_18631.memoize_lazy);
                    normalize_pure_lets =
                      (uu___335_18631.normalize_pure_lets)
                  }
                else
                  (let uu___336_18634 = cfg  in
                   {
                     steps =
                       (let uu___337_18637 = cfg.steps  in
                        {
                          beta = (uu___337_18637.beta);
                          iota = (uu___337_18637.iota);
                          zeta = false;
                          weak = (uu___337_18637.weak);
                          hnf = (uu___337_18637.hnf);
                          primops = (uu___337_18637.primops);
                          do_not_unfold_pure_lets =
                            (uu___337_18637.do_not_unfold_pure_lets);
                          unfold_until = (uu___337_18637.unfold_until);
                          unfold_only = (uu___337_18637.unfold_only);
                          unfold_fully = (uu___337_18637.unfold_fully);
                          unfold_attr = (uu___337_18637.unfold_attr);
                          unfold_tac = (uu___337_18637.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___337_18637.pure_subterms_within_computations);
                          simplify = (uu___337_18637.simplify);
                          erase_universes = (uu___337_18637.erase_universes);
                          allow_unbound_universes =
                            (uu___337_18637.allow_unbound_universes);
                          reify_ = (uu___337_18637.reify_);
                          compress_uvars = (uu___337_18637.compress_uvars);
                          no_full_norm = (uu___337_18637.no_full_norm);
                          check_no_uvars = (uu___337_18637.check_no_uvars);
                          unmeta = (uu___337_18637.unmeta);
                          unascribe = (uu___337_18637.unascribe);
                          in_full_norm_request =
                            (uu___337_18637.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___337_18637.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___336_18634.tcenv);
                     debug = (uu___336_18634.debug);
                     delta_level = (uu___336_18634.delta_level);
                     primitive_steps = (uu___336_18634.primitive_steps);
                     strong = (uu___336_18634.strong);
                     memoize_lazy = (uu___336_18634.memoize_lazy);
                     normalize_pure_lets =
                       (uu___336_18634.normalize_pure_lets)
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
                  (fun uu____18671  ->
                     let uu____18672 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18673 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18672
                       uu____18673);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18675 =
                   let uu____18676 = FStar_Syntax_Subst.compress head3  in
                   uu____18676.FStar_Syntax_Syntax.n  in
                 match uu____18675 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18694 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18694
                        in
                     let uu____18695 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18695 with
                      | (uu____18696,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18706 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18716 =
                                   let uu____18717 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18717.FStar_Syntax_Syntax.n  in
                                 match uu____18716 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18723,uu____18724))
                                     ->
                                     let uu____18733 =
                                       let uu____18734 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18734.FStar_Syntax_Syntax.n  in
                                     (match uu____18733 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18740,msrc,uu____18742))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18751 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18751
                                      | uu____18752 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18753 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18754 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18754 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___338_18759 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___338_18759.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___338_18759.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___338_18759.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___338_18759.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___338_18759.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18760 = FStar_List.tl stack  in
                                    let uu____18761 =
                                      let uu____18762 =
                                        let uu____18769 =
                                          let uu____18770 =
                                            let uu____18783 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18783)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18770
                                           in
                                        FStar_Syntax_Syntax.mk uu____18769
                                         in
                                      uu____18762
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18760 uu____18761
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18799 =
                                      let uu____18800 = is_return body  in
                                      match uu____18800 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18804;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18805;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18808 -> false  in
                                    if uu____18799
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
                                         let uu____18829 =
                                           let uu____18836 =
                                             let uu____18837 =
                                               let uu____18856 =
                                                 let uu____18865 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18865]  in
                                               (uu____18856, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18837
                                              in
                                           FStar_Syntax_Syntax.mk uu____18836
                                            in
                                         uu____18829
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18907 =
                                           let uu____18908 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18908.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18907 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18914::uu____18915::[])
                                             ->
                                             let uu____18920 =
                                               let uu____18927 =
                                                 let uu____18928 =
                                                   let uu____18935 =
                                                     let uu____18936 =
                                                       let uu____18937 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18937
                                                        in
                                                     let uu____18938 =
                                                       let uu____18941 =
                                                         let uu____18942 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18942
                                                          in
                                                       [uu____18941]  in
                                                     uu____18936 ::
                                                       uu____18938
                                                      in
                                                   (bind1, uu____18935)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18928
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18927
                                                in
                                             uu____18920
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18948 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18962 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18962
                                         then
                                           let uu____18973 =
                                             let uu____18982 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18982
                                              in
                                           let uu____18983 =
                                             let uu____18994 =
                                               let uu____19003 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____19003
                                                in
                                             [uu____18994]  in
                                           uu____18973 :: uu____18983
                                         else []  in
                                       let reified =
                                         let uu____19040 =
                                           let uu____19047 =
                                             let uu____19048 =
                                               let uu____19065 =
                                                 let uu____19076 =
                                                   let uu____19087 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____19096 =
                                                     let uu____19107 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____19107]  in
                                                   uu____19087 :: uu____19096
                                                    in
                                                 let uu____19140 =
                                                   let uu____19151 =
                                                     let uu____19162 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____19171 =
                                                       let uu____19182 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____19191 =
                                                         let uu____19202 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____19211 =
                                                           let uu____19222 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____19222]  in
                                                         uu____19202 ::
                                                           uu____19211
                                                          in
                                                       uu____19182 ::
                                                         uu____19191
                                                        in
                                                     uu____19162 ::
                                                       uu____19171
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____19151
                                                    in
                                                 FStar_List.append
                                                   uu____19076 uu____19140
                                                  in
                                               (bind_inst, uu____19065)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____19048
                                              in
                                           FStar_Syntax_Syntax.mk uu____19047
                                            in
                                         uu____19040
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____19306  ->
                                            let uu____19307 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____19308 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____19307 uu____19308);
                                       (let uu____19309 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____19309 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____19337 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____19337
                        in
                     let uu____19338 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____19338 with
                      | (uu____19339,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____19376 =
                                  let uu____19377 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____19377.FStar_Syntax_Syntax.n  in
                                match uu____19376 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____19381) -> t2
                                | uu____19386 -> head4  in
                              let uu____19387 =
                                let uu____19388 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____19388.FStar_Syntax_Syntax.n  in
                              match uu____19387 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____19394 -> FStar_Pervasives_Native.None
                               in
                            let uu____19395 = maybe_extract_fv head4  in
                            match uu____19395 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____19405 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____19405
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____19410 = maybe_extract_fv head5
                                     in
                                  match uu____19410 with
                                  | FStar_Pervasives_Native.Some uu____19415
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____19416 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____19421 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____19438 =
                              match uu____19438 with
                              | (e,q) ->
                                  let uu____19451 =
                                    let uu____19452 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____19452.FStar_Syntax_Syntax.n  in
                                  (match uu____19451 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____19467 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____19467
                                   | uu____19468 -> false)
                               in
                            let uu____19469 =
                              let uu____19470 =
                                let uu____19481 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____19481 :: args  in
                              FStar_Util.for_some is_arg_impure uu____19470
                               in
                            if uu____19469
                            then
                              let uu____19506 =
                                let uu____19507 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____19507
                                 in
                              failwith uu____19506
                            else ());
                           (let uu____19509 = maybe_unfold_action head_app
                               in
                            match uu____19509 with
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
                                   (fun uu____19554  ->
                                      let uu____19555 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____19556 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____19555 uu____19556);
                                 (let uu____19557 = FStar_List.tl stack  in
                                  norm cfg env uu____19557 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____19559) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____19583 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____19583  in
                     (log cfg
                        (fun uu____19587  ->
                           let uu____19588 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____19588);
                      (let uu____19589 = FStar_List.tl stack  in
                       norm cfg env uu____19589 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____19710  ->
                               match uu____19710 with
                               | (pat,wopt,tm) ->
                                   let uu____19758 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19758)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19790 = FStar_List.tl stack  in
                     norm cfg env uu____19790 tm
                 | uu____19791 -> fallback ())

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
              (fun uu____19805  ->
                 let uu____19806 = FStar_Ident.string_of_lid msrc  in
                 let uu____19807 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19808 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19806
                   uu____19807 uu____19808);
            (let uu____19809 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19809
             then
               let ed =
                 let uu____19811 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19811  in
               let uu____19812 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19812 with
               | (uu____19813,return_repr) ->
                   let return_inst =
                     let uu____19826 =
                       let uu____19827 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19827.FStar_Syntax_Syntax.n  in
                     match uu____19826 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19833::[]) ->
                         let uu____19838 =
                           let uu____19845 =
                             let uu____19846 =
                               let uu____19853 =
                                 let uu____19854 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19854]  in
                               (return_tm, uu____19853)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19846  in
                           FStar_Syntax_Syntax.mk uu____19845  in
                         uu____19838 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19860 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19863 =
                     let uu____19870 =
                       let uu____19871 =
                         let uu____19888 =
                           let uu____19899 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19908 =
                             let uu____19919 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19919]  in
                           uu____19899 :: uu____19908  in
                         (return_inst, uu____19888)  in
                       FStar_Syntax_Syntax.Tm_app uu____19871  in
                     FStar_Syntax_Syntax.mk uu____19870  in
                   uu____19863 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19968 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19968 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19971 =
                      let uu____19972 = FStar_Ident.text_of_lid msrc  in
                      let uu____19973 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19972 uu____19973
                       in
                    failwith uu____19971
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19974;
                      FStar_TypeChecker_Env.mtarget = uu____19975;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19976;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19998 =
                      let uu____19999 = FStar_Ident.text_of_lid msrc  in
                      let uu____20000 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19999 uu____20000
                       in
                    failwith uu____19998
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____20001;
                      FStar_TypeChecker_Env.mtarget = uu____20002;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____20003;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____20038 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____20039 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____20038 t FStar_Syntax_Syntax.tun uu____20039))

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                                FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____20109  ->
                   match uu____20109 with
                   | (a,imp) ->
                       let uu____20128 = norm cfg env [] a  in
                       (uu____20128, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____20138  ->
             let uu____20139 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____20140 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____20139 uu____20140);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20164 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____20164
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___339_20167 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___339_20167.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___339_20167.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20189 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____20189
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___340_20192 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___340_20192.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___340_20192.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____20237  ->
                      match uu____20237 with
                      | (a,i) ->
                          let uu____20256 = norm cfg env [] a  in
                          (uu____20256, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___253_20278  ->
                       match uu___253_20278 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____20282 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____20282
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___341_20290 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___342_20293 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___342_20293.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___341_20290.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___341_20290.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____20296  ->
        match uu____20296 with
        | (x,imp) ->
            let uu____20303 =
              let uu___343_20304 = x  in
              let uu____20305 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___343_20304.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___343_20304.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____20305
              }  in
            (uu____20303, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____20313 =
          FStar_List.fold_left
            (fun uu____20347  ->
               fun b  ->
                 match uu____20347 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____20313 with | (nbs,uu____20427) -> FStar_List.rev nbs

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
            let uu____20459 =
              let uu___344_20460 = rc  in
              let uu____20461 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___344_20460.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____20461;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___344_20460.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____20459
        | uu____20470 -> lopt

and (maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
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
            (let uu____20493 = FStar_Syntax_Print.term_to_string tm  in
             let uu____20494 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____20493
               uu____20494)
          else ();
          tm'

and (maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____20520 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____20520
          then tm1
          else
            (let w t =
               let uu___345_20534 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___345_20534.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___345_20534.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____20545 =
                 let uu____20546 = FStar_Syntax_Util.unmeta t  in
                 uu____20546.FStar_Syntax_Syntax.n  in
               match uu____20545 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____20553 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____20614)::args1,(bv,uu____20617)::bs1) ->
                   let uu____20671 =
                     let uu____20672 = FStar_Syntax_Subst.compress t  in
                     uu____20672.FStar_Syntax_Syntax.n  in
                   (match uu____20671 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____20676 -> false)
               | ([],[]) -> true
               | (uu____20705,uu____20706) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____20755 = FStar_Syntax_Print.term_to_string t  in
                  let uu____20756 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____20755
                    uu____20756)
               else ();
               (let uu____20758 = FStar_Syntax_Util.head_and_args' t  in
                match uu____20758 with
                | (hd1,args) ->
                    let uu____20797 =
                      let uu____20798 = FStar_Syntax_Subst.compress hd1  in
                      uu____20798.FStar_Syntax_Syntax.n  in
                    (match uu____20797 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____20805 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____20806 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____20807 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____20805 uu____20806 uu____20807)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____20809 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____20826 = FStar_Syntax_Print.term_to_string t  in
                  let uu____20827 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____20826
                    uu____20827)
               else ();
               (let uu____20829 = FStar_Syntax_Util.is_squash t  in
                match uu____20829 with
                | FStar_Pervasives_Native.Some (uu____20840,t') ->
                    is_applied bs t'
                | uu____20852 ->
                    let uu____20861 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____20861 with
                     | FStar_Pervasives_Native.Some (uu____20872,t') ->
                         is_applied bs t'
                     | uu____20884 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20908 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20908 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20915)::(q,uu____20917)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20959 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20960 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20959 uu____20960)
                    else ();
                    (let uu____20962 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20962 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20967 =
                           let uu____20968 = FStar_Syntax_Subst.compress p
                              in
                           uu____20968.FStar_Syntax_Syntax.n  in
                         (match uu____20967 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20976 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20976))
                          | uu____20979 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20982)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____21007 =
                           let uu____21008 = FStar_Syntax_Subst.compress p1
                              in
                           uu____21008.FStar_Syntax_Syntax.n  in
                         (match uu____21007 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____21016 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____21016))
                          | uu____21019 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____21023 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____21023 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____21028 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____21028 with
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
                                     let uu____21039 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21039))
                               | uu____21042 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____21047)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____21072 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____21072 with
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
                                     let uu____21083 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21083))
                               | uu____21086 -> FStar_Pervasives_Native.None)
                          | uu____21089 -> FStar_Pervasives_Native.None)
                     | uu____21092 -> FStar_Pervasives_Native.None))
               | uu____21095 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____21108 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____21108 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____21114)::[],uu____21115,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____21134 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____21135 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____21134
                         uu____21135)
                    else ();
                    is_quantified_const bv phi')
               | uu____21137 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____21150 =
                 let uu____21151 = FStar_Syntax_Subst.compress phi  in
                 uu____21151.FStar_Syntax_Syntax.n  in
               match uu____21150 with
               | FStar_Syntax_Syntax.Tm_match (uu____21156,br::brs) ->
                   let uu____21223 = br  in
                   (match uu____21223 with
                    | (uu____21240,uu____21241,e) ->
                        let r =
                          let uu____21262 = simp_t e  in
                          match uu____21262 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____21268 =
                                FStar_List.for_all
                                  (fun uu____21286  ->
                                     match uu____21286 with
                                     | (uu____21299,uu____21300,e') ->
                                         let uu____21314 = simp_t e'  in
                                         uu____21314 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____21268
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____21322 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____21331 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____21331
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____21366 =
                 match uu____21366 with
                 | (t1,q) ->
                     let uu____21387 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____21387 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____21419 -> (t1, q))
                  in
               let uu____21432 = FStar_Syntax_Util.head_and_args t  in
               match uu____21432 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____21510 =
                 let uu____21511 = FStar_Syntax_Util.unmeta ty  in
                 uu____21511.FStar_Syntax_Syntax.n  in
               match uu____21510 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____21515) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____21520,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____21544 -> false  in
             let simplify1 arg =
               let uu____21575 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____21575, arg)  in
             let uu____21588 = is_forall_const tm1  in
             match uu____21588 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____21593 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____21594 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____21593
                       uu____21594)
                  else ();
                  (let uu____21596 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____21596))
             | FStar_Pervasives_Native.None  ->
                 let uu____21597 =
                   let uu____21598 = FStar_Syntax_Subst.compress tm1  in
                   uu____21598.FStar_Syntax_Syntax.n  in
                 (match uu____21597 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____21602;
                              FStar_Syntax_Syntax.vars = uu____21603;_},uu____21604);
                         FStar_Syntax_Syntax.pos = uu____21605;
                         FStar_Syntax_Syntax.vars = uu____21606;_},args)
                      ->
                      let uu____21636 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21636
                      then
                        let uu____21637 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21637 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21692)::
                             (uu____21693,(arg,uu____21695))::[] ->
                             maybe_auto_squash arg
                         | (uu____21760,(arg,uu____21762))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21763)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21828)::uu____21829::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21892::(FStar_Pervasives_Native.Some (false
                                         ),uu____21893)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21956 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21972 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21972
                         then
                           let uu____21973 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21973 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22028)::uu____22029::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22092::(FStar_Pervasives_Native.Some (true
                                           ),uu____22093)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22156)::(uu____22157,(arg,uu____22159))::[]
                               -> maybe_auto_squash arg
                           | (uu____22224,(arg,uu____22226))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22227)::[]
                               -> maybe_auto_squash arg
                           | uu____22292 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22308 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22308
                            then
                              let uu____22309 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22309 with
                              | uu____22364::(FStar_Pervasives_Native.Some
                                              (true ),uu____22365)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22428)::uu____22429::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22492)::(uu____22493,(arg,uu____22495))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22560,(p,uu____22562))::(uu____22563,
                                                                (q,uu____22565))::[]
                                  ->
                                  let uu____22630 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22630
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22632 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22648 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22648
                               then
                                 let uu____22649 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22649 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22704)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22705)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22770)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22771)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22836)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22837)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22902)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22903)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22968,(arg,uu____22970))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22971)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23036)::(uu____23037,(arg,uu____23039))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23104,(arg,uu____23106))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23107)::[]
                                     ->
                                     let uu____23172 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23172
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23173)::(uu____23174,(arg,uu____23176))::[]
                                     ->
                                     let uu____23241 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23241
                                 | (uu____23242,(p,uu____23244))::(uu____23245,
                                                                   (q,uu____23247))::[]
                                     ->
                                     let uu____23312 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23312
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23314 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23330 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23330
                                  then
                                    let uu____23331 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23331 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23386)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23425)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23464 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23480 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23480
                                     then
                                       match args with
                                       | (t,uu____23482)::[] ->
                                           let uu____23507 =
                                             let uu____23508 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23508.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23507 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23511::[],body,uu____23513)
                                                ->
                                                let uu____23548 = simp_t body
                                                   in
                                                (match uu____23548 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23551 -> tm1)
                                            | uu____23554 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23556))::(t,uu____23558)::[]
                                           ->
                                           let uu____23597 =
                                             let uu____23598 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23598.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23597 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23601::[],body,uu____23603)
                                                ->
                                                let uu____23638 = simp_t body
                                                   in
                                                (match uu____23638 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23641 -> tm1)
                                            | uu____23644 -> tm1)
                                       | uu____23645 -> tm1
                                     else
                                       (let uu____23657 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23657
                                        then
                                          match args with
                                          | (t,uu____23659)::[] ->
                                              let uu____23684 =
                                                let uu____23685 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23685.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23684 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23688::[],body,uu____23690)
                                                   ->
                                                   let uu____23725 =
                                                     simp_t body  in
                                                   (match uu____23725 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23728 -> tm1)
                                               | uu____23731 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23733))::(t,uu____23735)::[]
                                              ->
                                              let uu____23774 =
                                                let uu____23775 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23775.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23774 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23778::[],body,uu____23780)
                                                   ->
                                                   let uu____23815 =
                                                     simp_t body  in
                                                   (match uu____23815 with
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
                                                    | uu____23818 -> tm1)
                                               | uu____23821 -> tm1)
                                          | uu____23822 -> tm1
                                        else
                                          (let uu____23834 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23834
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23835;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23836;_},uu____23837)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23862;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23863;_},uu____23864)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23889 -> tm1
                                           else
                                             (let uu____23901 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____23901 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____23921 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____23933;
                         FStar_Syntax_Syntax.vars = uu____23934;_},args)
                      ->
                      let uu____23960 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____23960
                      then
                        let uu____23961 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____23961 with
                         | (FStar_Pervasives_Native.Some (true ),uu____24016)::
                             (uu____24017,(arg,uu____24019))::[] ->
                             maybe_auto_squash arg
                         | (uu____24084,(arg,uu____24086))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____24087)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____24152)::uu____24153::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____24216::(FStar_Pervasives_Native.Some (false
                                         ),uu____24217)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____24280 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____24296 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____24296
                         then
                           let uu____24297 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____24297 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____24352)::uu____24353::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____24416::(FStar_Pervasives_Native.Some (true
                                           ),uu____24417)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____24480)::(uu____24481,(arg,uu____24483))::[]
                               -> maybe_auto_squash arg
                           | (uu____24548,(arg,uu____24550))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____24551)::[]
                               -> maybe_auto_squash arg
                           | uu____24616 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____24632 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____24632
                            then
                              let uu____24633 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____24633 with
                              | uu____24688::(FStar_Pervasives_Native.Some
                                              (true ),uu____24689)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____24752)::uu____24753::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____24816)::(uu____24817,(arg,uu____24819))::[]
                                  -> maybe_auto_squash arg
                              | (uu____24884,(p,uu____24886))::(uu____24887,
                                                                (q,uu____24889))::[]
                                  ->
                                  let uu____24954 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____24954
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____24956 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____24972 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____24972
                               then
                                 let uu____24973 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____24973 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25028)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25029)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25094)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25095)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25160)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25161)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25226)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25227)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____25292,(arg,uu____25294))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____25295)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25360)::(uu____25361,(arg,uu____25363))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____25428,(arg,uu____25430))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____25431)::[]
                                     ->
                                     let uu____25496 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25496
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25497)::(uu____25498,(arg,uu____25500))::[]
                                     ->
                                     let uu____25565 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25565
                                 | (uu____25566,(p,uu____25568))::(uu____25569,
                                                                   (q,uu____25571))::[]
                                     ->
                                     let uu____25636 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____25636
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____25638 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____25654 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____25654
                                  then
                                    let uu____25655 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____25655 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____25710)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____25749)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____25788 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____25804 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____25804
                                     then
                                       match args with
                                       | (t,uu____25806)::[] ->
                                           let uu____25831 =
                                             let uu____25832 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____25832.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____25831 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____25835::[],body,uu____25837)
                                                ->
                                                let uu____25872 = simp_t body
                                                   in
                                                (match uu____25872 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____25875 -> tm1)
                                            | uu____25878 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____25880))::(t,uu____25882)::[]
                                           ->
                                           let uu____25921 =
                                             let uu____25922 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____25922.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____25921 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____25925::[],body,uu____25927)
                                                ->
                                                let uu____25962 = simp_t body
                                                   in
                                                (match uu____25962 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____25965 -> tm1)
                                            | uu____25968 -> tm1)
                                       | uu____25969 -> tm1
                                     else
                                       (let uu____25981 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____25981
                                        then
                                          match args with
                                          | (t,uu____25983)::[] ->
                                              let uu____26008 =
                                                let uu____26009 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26009.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26008 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26012::[],body,uu____26014)
                                                   ->
                                                   let uu____26049 =
                                                     simp_t body  in
                                                   (match uu____26049 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____26052 -> tm1)
                                               | uu____26055 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____26057))::(t,uu____26059)::[]
                                              ->
                                              let uu____26098 =
                                                let uu____26099 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26099.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26098 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26102::[],body,uu____26104)
                                                   ->
                                                   let uu____26139 =
                                                     simp_t body  in
                                                   (match uu____26139 with
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
                                                    | uu____26142 -> tm1)
                                               | uu____26145 -> tm1)
                                          | uu____26146 -> tm1
                                        else
                                          (let uu____26158 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____26158
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26159;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26160;_},uu____26161)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26186;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26187;_},uu____26188)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____26213 -> tm1
                                           else
                                             (let uu____26225 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____26225 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____26245 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____26262 = simp_t t  in
                      (match uu____26262 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____26265 ->
                      let uu____26288 = is_const_match tm1  in
                      (match uu____26288 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____26291 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____26301  ->
               (let uu____26303 = FStar_Syntax_Print.tag_of_term t  in
                let uu____26304 = FStar_Syntax_Print.term_to_string t  in
                let uu____26305 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____26312 =
                  let uu____26313 =
                    let uu____26316 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____26316
                     in
                  stack_to_string uu____26313  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____26303 uu____26304 uu____26305 uu____26312);
               (let uu____26339 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____26339
                then
                  let uu____26340 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____26340 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____26347 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____26348 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____26349 =
                          let uu____26350 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____26350
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____26347
                          uu____26348 uu____26349);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____26368 =
                     let uu____26369 =
                       let uu____26370 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____26370  in
                     FStar_Util.string_of_int uu____26369  in
                   let uu____26375 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____26376 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____26368 uu____26375 uu____26376)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____26382,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____26433  ->
                     let uu____26434 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____26434);
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
               let uu____26472 =
                 let uu___346_26473 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___346_26473.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___346_26473.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____26472
           | (Arg (Univ uu____26476,uu____26477,uu____26478))::uu____26479 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____26482,uu____26483))::uu____26484 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____26499,uu____26500),aq,r))::stack1
               when
               let uu____26550 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____26550 ->
               let t2 =
                 let uu____26554 =
                   let uu____26559 =
                     let uu____26560 = closure_as_term cfg env_arg tm  in
                     (uu____26560, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____26559  in
                 uu____26554 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____26572),aq,r))::stack1 ->
               (log cfg
                  (fun uu____26625  ->
                     let uu____26626 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____26626);
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
                  (let uu____26640 = FStar_ST.op_Bang m  in
                   match uu____26640 with
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
                   | FStar_Pervasives_Native.Some (uu____26785,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____26840 =
                 log cfg
                   (fun uu____26844  ->
                      let uu____26845 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____26845);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____26853 =
                 let uu____26854 = FStar_Syntax_Subst.compress t1  in
                 uu____26854.FStar_Syntax_Syntax.n  in
               (match uu____26853 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____26881 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____26881  in
                    (log cfg
                       (fun uu____26885  ->
                          let uu____26886 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____26886);
                     (let uu____26887 = FStar_List.tl stack  in
                      norm cfg env1 uu____26887 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____26888);
                       FStar_Syntax_Syntax.pos = uu____26889;
                       FStar_Syntax_Syntax.vars = uu____26890;_},(e,uu____26892)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____26931 when
                    (cfg.steps).primops ->
                    let uu____26948 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____26948 with
                     | (hd1,args) ->
                         let uu____26991 =
                           let uu____26992 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____26992.FStar_Syntax_Syntax.n  in
                         (match uu____26991 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____26996 = find_prim_step cfg fv  in
                              (match uu____26996 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____26999; arity = uu____27000;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____27002;
                                     requires_binder_substitution =
                                       uu____27003;
                                     interpretation = uu____27004;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____27021 -> fallback " (3)" ())
                          | uu____27024 -> fallback " (4)" ()))
                | uu____27025 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____27050  ->
                     let uu____27051 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____27051);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____27060 =
                   log cfg1
                     (fun uu____27065  ->
                        let uu____27066 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____27067 =
                          let uu____27068 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____27095  ->
                                    match uu____27095 with
                                    | (p,uu____27105,uu____27106) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____27068
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____27066 uu____27067);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___254_27123  ->
                                match uu___254_27123 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____27124 -> false))
                         in
                      let steps =
                        let uu___347_27126 = cfg1.steps  in
                        {
                          beta = (uu___347_27126.beta);
                          iota = (uu___347_27126.iota);
                          zeta = false;
                          weak = (uu___347_27126.weak);
                          hnf = (uu___347_27126.hnf);
                          primops = (uu___347_27126.primops);
                          do_not_unfold_pure_lets =
                            (uu___347_27126.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___347_27126.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___347_27126.pure_subterms_within_computations);
                          simplify = (uu___347_27126.simplify);
                          erase_universes = (uu___347_27126.erase_universes);
                          allow_unbound_universes =
                            (uu___347_27126.allow_unbound_universes);
                          reify_ = (uu___347_27126.reify_);
                          compress_uvars = (uu___347_27126.compress_uvars);
                          no_full_norm = (uu___347_27126.no_full_norm);
                          check_no_uvars = (uu___347_27126.check_no_uvars);
                          unmeta = (uu___347_27126.unmeta);
                          unascribe = (uu___347_27126.unascribe);
                          in_full_norm_request =
                            (uu___347_27126.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___347_27126.weakly_reduce_scrutinee)
                        }  in
                      let uu___348_27131 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___348_27131.tcenv);
                        debug = (uu___348_27131.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___348_27131.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___348_27131.memoize_lazy);
                        normalize_pure_lets =
                          (uu___348_27131.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____27203 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____27232 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____27316  ->
                                    fun uu____27317  ->
                                      match (uu____27316, uu____27317) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____27456 = norm_pat env3 p1
                                             in
                                          (match uu____27456 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____27232 with
                           | (pats1,env3) ->
                               ((let uu___349_27618 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___349_27618.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___350_27637 = x  in
                            let uu____27638 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___350_27637.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___350_27637.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27638
                            }  in
                          ((let uu___351_27652 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___351_27652.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___352_27663 = x  in
                            let uu____27664 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___352_27663.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___352_27663.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27664
                            }  in
                          ((let uu___353_27678 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___353_27678.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___354_27694 = x  in
                            let uu____27695 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___354_27694.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___354_27694.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27695
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___355_27710 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___355_27710.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____27754 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____27784 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____27784 with
                                  | (p,wopt,e) ->
                                      let uu____27804 = norm_pat env1 p  in
                                      (match uu____27804 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____27859 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____27859
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____27876 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____27876
                      then
                        norm
                          (let uu___356_27881 = cfg1  in
                           {
                             steps =
                               (let uu___357_27884 = cfg1.steps  in
                                {
                                  beta = (uu___357_27884.beta);
                                  iota = (uu___357_27884.iota);
                                  zeta = (uu___357_27884.zeta);
                                  weak = (uu___357_27884.weak);
                                  hnf = (uu___357_27884.hnf);
                                  primops = (uu___357_27884.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___357_27884.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___357_27884.unfold_until);
                                  unfold_only = (uu___357_27884.unfold_only);
                                  unfold_fully =
                                    (uu___357_27884.unfold_fully);
                                  unfold_attr = (uu___357_27884.unfold_attr);
                                  unfold_tac = (uu___357_27884.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___357_27884.pure_subterms_within_computations);
                                  simplify = (uu___357_27884.simplify);
                                  erase_universes =
                                    (uu___357_27884.erase_universes);
                                  allow_unbound_universes =
                                    (uu___357_27884.allow_unbound_universes);
                                  reify_ = (uu___357_27884.reify_);
                                  compress_uvars =
                                    (uu___357_27884.compress_uvars);
                                  no_full_norm =
                                    (uu___357_27884.no_full_norm);
                                  check_no_uvars =
                                    (uu___357_27884.check_no_uvars);
                                  unmeta = (uu___357_27884.unmeta);
                                  unascribe = (uu___357_27884.unascribe);
                                  in_full_norm_request =
                                    (uu___357_27884.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___356_27881.tcenv);
                             debug = (uu___356_27881.debug);
                             delta_level = (uu___356_27881.delta_level);
                             primitive_steps =
                               (uu___356_27881.primitive_steps);
                             strong = (uu___356_27881.strong);
                             memoize_lazy = (uu___356_27881.memoize_lazy);
                             normalize_pure_lets =
                               (uu___356_27881.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____27886 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____27886)
                    in
                 let rec is_cons head1 =
                   let uu____27911 =
                     let uu____27912 = FStar_Syntax_Subst.compress head1  in
                     uu____27912.FStar_Syntax_Syntax.n  in
                   match uu____27911 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____27916) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____27921 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____27922;
                         FStar_Syntax_Syntax.fv_delta = uu____27923;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____27924;
                         FStar_Syntax_Syntax.fv_delta = uu____27925;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____27926);_}
                       -> true
                   | uu____27933 -> false  in
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
                   let uu____28096 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____28096 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____28189 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____28228 ->
                                 let uu____28229 =
                                   let uu____28230 = is_cons head1  in
                                   Prims.op_Negation uu____28230  in
                                 FStar_Util.Inr uu____28229)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____28255 =
                              let uu____28256 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____28256.FStar_Syntax_Syntax.n  in
                            (match uu____28255 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____28274 ->
                                 let uu____28275 =
                                   let uu____28276 = is_cons head1  in
                                   Prims.op_Negation uu____28276  in
                                 FStar_Util.Inr uu____28275))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____28359)::rest_a,(p1,uu____28362)::rest_p) ->
                       let uu____28416 = matches_pat t2 p1  in
                       (match uu____28416 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____28465 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____28585 = matches_pat scrutinee1 p1  in
                       (match uu____28585 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____28625  ->
                                  let uu____28626 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____28627 =
                                    let uu____28628 =
                                      FStar_List.map
                                        (fun uu____28638  ->
                                           match uu____28638 with
                                           | (uu____28643,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____28628
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____28626 uu____28627);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____28675  ->
                                       match uu____28675 with
                                       | (bv,t2) ->
                                           let uu____28698 =
                                             let uu____28705 =
                                               let uu____28708 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____28708
                                                in
                                             let uu____28709 =
                                               let uu____28710 =
                                                 let uu____28741 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____28741, false)
                                                  in
                                               Clos uu____28710  in
                                             (uu____28705, uu____28709)  in
                                           uu____28698 :: env2) env1 s
                                 in
                              let uu____28854 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____28854)))
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
    let uu____28881 =
      let uu____28884 = FStar_ST.op_Bang plugins  in p :: uu____28884  in
    FStar_ST.op_Colon_Equals plugins uu____28881  in
  let retrieve uu____28992 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____29069  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___255_29110  ->
                  match uu___255_29110 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | uu____29114 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____29120 -> d  in
        let uu____29123 = to_fsteps s  in
        let uu____29124 =
          let uu____29125 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____29126 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____29127 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____29128 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____29129 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____29130 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____29131 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____29125;
            primop = uu____29126;
            unfolding = uu____29127;
            b380 = uu____29128;
            wpe = uu____29129;
            norm_delayed = uu____29130;
            print_normalized = uu____29131
          }  in
        let uu____29132 =
          let uu____29135 =
            let uu____29138 = retrieve_plugins ()  in
            FStar_List.append uu____29138 psteps  in
          add_steps built_in_primitive_steps uu____29135  in
        let uu____29141 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____29143 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____29143)
           in
        {
          steps = uu____29123;
          tcenv = e;
          debug = uu____29124;
          delta_level = d1;
          primitive_steps = uu____29132;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____29141
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
            (fun uu____29192  ->
               let uu____29193 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "Starting normalizer for (%s)\n" uu____29193);
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
      fun t  -> let uu____29230 = config s e  in norm_comp uu____29230 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____29247 = config [] env  in norm_universe uu____29247 [] u
  
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
        let uu____29271 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29271  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____29278 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___358_29297 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___358_29297.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___358_29297.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____29304 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____29304
          then
            let ct1 =
              let uu____29306 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____29306 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____29313 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____29313
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___359_29317 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___359_29317.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___359_29317.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___359_29317.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___360_29319 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___360_29319.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___360_29319.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___360_29319.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___360_29319.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___361_29320 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___361_29320.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___361_29320.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____29322 -> c
  
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
        let uu____29340 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29340  in
      let uu____29347 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____29347
      then
        let uu____29348 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____29348 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____29354  ->
                 let uu____29355 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____29355)
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
            ((let uu____29376 =
                let uu____29381 =
                  let uu____29382 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29382
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29381)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____29376);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____29397 = config [AllowUnboundUniverses] env  in
          norm_comp uu____29397 [] c
        with
        | e ->
            ((let uu____29410 =
                let uu____29415 =
                  let uu____29416 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29416
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29415)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____29410);
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
                   let uu____29461 =
                     let uu____29462 =
                       let uu____29469 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____29469)  in
                     FStar_Syntax_Syntax.Tm_refine uu____29462  in
                   mk uu____29461 t01.FStar_Syntax_Syntax.pos
               | uu____29474 -> t2)
          | uu____29475 -> t2  in
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
        let uu____29554 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____29554 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____29591 ->
                 let uu____29600 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____29600 with
                  | (actuals,uu____29610,uu____29611) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____29629 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____29629 with
                         | (binders,args) ->
                             let uu____29640 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____29640
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
      | uu____29654 ->
          let uu____29655 = FStar_Syntax_Util.head_and_args t  in
          (match uu____29655 with
           | (head1,args) ->
               let uu____29698 =
                 let uu____29699 = FStar_Syntax_Subst.compress head1  in
                 uu____29699.FStar_Syntax_Syntax.n  in
               (match uu____29698 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____29720 =
                      let uu____29735 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____29735  in
                    (match uu____29720 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____29773 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___366_29781 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___366_29781.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___366_29781.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___366_29781.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___366_29781.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___366_29781.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___366_29781.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___366_29781.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___366_29781.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___366_29781.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___366_29781.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___366_29781.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___366_29781.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___366_29781.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___366_29781.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___366_29781.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___366_29781.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___366_29781.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___366_29781.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___366_29781.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___366_29781.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___366_29781.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___366_29781.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___366_29781.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___366_29781.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___366_29781.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___366_29781.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___366_29781.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___366_29781.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___366_29781.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___366_29781.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___366_29781.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___366_29781.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___366_29781.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___366_29781.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___366_29781.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___366_29781.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___366_29781.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___366_29781.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____29773 with
                            | (uu____29782,ty,uu____29784) ->
                                eta_expand_with_type env t ty))
                | uu____29785 ->
                    let uu____29786 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___367_29794 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___367_29794.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___367_29794.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___367_29794.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___367_29794.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___367_29794.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___367_29794.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___367_29794.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___367_29794.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___367_29794.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___367_29794.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___367_29794.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___367_29794.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___367_29794.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___367_29794.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___367_29794.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___367_29794.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___367_29794.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___367_29794.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___367_29794.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___367_29794.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___367_29794.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___367_29794.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___367_29794.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___367_29794.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___367_29794.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___367_29794.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___367_29794.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___367_29794.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___367_29794.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___367_29794.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___367_29794.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___367_29794.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___367_29794.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___367_29794.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___367_29794.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___367_29794.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___367_29794.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___367_29794.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____29786 with
                     | (uu____29795,ty,uu____29797) ->
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
      let uu___368_29878 = x  in
      let uu____29879 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___368_29878.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___368_29878.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____29879
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____29882 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____29905 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____29906 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____29907 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____29908 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____29915 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____29916 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____29917 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___369_29951 = rc  in
          let uu____29952 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____29961 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___369_29951.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____29952;
            FStar_Syntax_Syntax.residual_flags = uu____29961
          }  in
        let uu____29964 =
          let uu____29965 =
            let uu____29984 = elim_delayed_subst_binders bs  in
            let uu____29993 = elim_delayed_subst_term t2  in
            let uu____29996 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____29984, uu____29993, uu____29996)  in
          FStar_Syntax_Syntax.Tm_abs uu____29965  in
        mk1 uu____29964
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____30033 =
          let uu____30034 =
            let uu____30049 = elim_delayed_subst_binders bs  in
            let uu____30058 = elim_delayed_subst_comp c  in
            (uu____30049, uu____30058)  in
          FStar_Syntax_Syntax.Tm_arrow uu____30034  in
        mk1 uu____30033
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____30077 =
          let uu____30078 =
            let uu____30085 = elim_bv bv  in
            let uu____30086 = elim_delayed_subst_term phi  in
            (uu____30085, uu____30086)  in
          FStar_Syntax_Syntax.Tm_refine uu____30078  in
        mk1 uu____30077
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____30117 =
          let uu____30118 =
            let uu____30135 = elim_delayed_subst_term t2  in
            let uu____30138 = elim_delayed_subst_args args  in
            (uu____30135, uu____30138)  in
          FStar_Syntax_Syntax.Tm_app uu____30118  in
        mk1 uu____30117
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___370_30210 = p  in
              let uu____30211 =
                let uu____30212 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____30212  in
              {
                FStar_Syntax_Syntax.v = uu____30211;
                FStar_Syntax_Syntax.p =
                  (uu___370_30210.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___371_30214 = p  in
              let uu____30215 =
                let uu____30216 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____30216  in
              {
                FStar_Syntax_Syntax.v = uu____30215;
                FStar_Syntax_Syntax.p =
                  (uu___371_30214.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___372_30223 = p  in
              let uu____30224 =
                let uu____30225 =
                  let uu____30232 = elim_bv x  in
                  let uu____30233 = elim_delayed_subst_term t0  in
                  (uu____30232, uu____30233)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____30225  in
              {
                FStar_Syntax_Syntax.v = uu____30224;
                FStar_Syntax_Syntax.p =
                  (uu___372_30223.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___373_30256 = p  in
              let uu____30257 =
                let uu____30258 =
                  let uu____30271 =
                    FStar_List.map
                      (fun uu____30294  ->
                         match uu____30294 with
                         | (x,b) ->
                             let uu____30307 = elim_pat x  in
                             (uu____30307, b)) pats
                     in
                  (fv, uu____30271)  in
                FStar_Syntax_Syntax.Pat_cons uu____30258  in
              {
                FStar_Syntax_Syntax.v = uu____30257;
                FStar_Syntax_Syntax.p =
                  (uu___373_30256.FStar_Syntax_Syntax.p)
              }
          | uu____30320 -> p  in
        let elim_branch uu____30344 =
          match uu____30344 with
          | (pat,wopt,t3) ->
              let uu____30370 = elim_pat pat  in
              let uu____30373 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____30376 = elim_delayed_subst_term t3  in
              (uu____30370, uu____30373, uu____30376)
           in
        let uu____30381 =
          let uu____30382 =
            let uu____30405 = elim_delayed_subst_term t2  in
            let uu____30408 = FStar_List.map elim_branch branches  in
            (uu____30405, uu____30408)  in
          FStar_Syntax_Syntax.Tm_match uu____30382  in
        mk1 uu____30381
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____30539 =
          match uu____30539 with
          | (tc,topt) ->
              let uu____30574 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____30584 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____30584
                | FStar_Util.Inr c ->
                    let uu____30586 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____30586
                 in
              let uu____30587 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____30574, uu____30587)
           in
        let uu____30596 =
          let uu____30597 =
            let uu____30624 = elim_delayed_subst_term t2  in
            let uu____30627 = elim_ascription a  in
            (uu____30624, uu____30627, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____30597  in
        mk1 uu____30596
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___374_30688 = lb  in
          let uu____30689 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____30692 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___374_30688.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___374_30688.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____30689;
            FStar_Syntax_Syntax.lbeff =
              (uu___374_30688.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____30692;
            FStar_Syntax_Syntax.lbattrs =
              (uu___374_30688.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___374_30688.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____30695 =
          let uu____30696 =
            let uu____30709 =
              let uu____30716 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____30716)  in
            let uu____30725 = elim_delayed_subst_term t2  in
            (uu____30709, uu____30725)  in
          FStar_Syntax_Syntax.Tm_let uu____30696  in
        mk1 uu____30695
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____30769 =
          let uu____30770 =
            let uu____30777 = elim_delayed_subst_term tm  in
            (uu____30777, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____30770  in
        mk1 uu____30769
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____30788 =
          let uu____30789 =
            let uu____30796 = elim_delayed_subst_term t2  in
            let uu____30799 = elim_delayed_subst_meta md  in
            (uu____30796, uu____30799)  in
          FStar_Syntax_Syntax.Tm_meta uu____30789  in
        mk1 uu____30788

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___256_30808  ->
         match uu___256_30808 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____30812 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____30812
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
        let uu____30835 =
          let uu____30836 =
            let uu____30845 = elim_delayed_subst_term t  in
            (uu____30845, uopt)  in
          FStar_Syntax_Syntax.Total uu____30836  in
        mk1 uu____30835
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____30862 =
          let uu____30863 =
            let uu____30872 = elim_delayed_subst_term t  in
            (uu____30872, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____30863  in
        mk1 uu____30862
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___375_30881 = ct  in
          let uu____30882 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____30885 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____30896 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___375_30881.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___375_30881.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____30882;
            FStar_Syntax_Syntax.effect_args = uu____30885;
            FStar_Syntax_Syntax.flags = uu____30896
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___257_30899  ->
    match uu___257_30899 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____30913 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____30913
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____30952 =
          let uu____30959 = elim_delayed_subst_term t  in (m, uu____30959)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____30952
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____30971 =
          let uu____30980 = elim_delayed_subst_term t  in
          (m1, m2, uu____30980)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____30971
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____31013  ->
         match uu____31013 with
         | (t,q) ->
             let uu____31032 = elim_delayed_subst_term t  in (uu____31032, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____31060  ->
         match uu____31060 with
         | (x,q) ->
             let uu____31079 =
               let uu___376_31080 = x  in
               let uu____31081 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___376_31080.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___376_31080.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____31081
               }  in
             (uu____31079, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
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
            | (uu____31187,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____31219,FStar_Util.Inl t) ->
                let uu____31241 =
                  let uu____31248 =
                    let uu____31249 =
                      let uu____31264 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____31264)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____31249  in
                  FStar_Syntax_Syntax.mk uu____31248  in
                uu____31241 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____31280 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____31280 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____31312 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____31385 ->
                    let uu____31386 =
                      let uu____31395 =
                        let uu____31396 = FStar_Syntax_Subst.compress t4  in
                        uu____31396.FStar_Syntax_Syntax.n  in
                      (uu____31395, tc)  in
                    (match uu____31386 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____31425) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____31472) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____31517,FStar_Util.Inl uu____31518) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____31549 -> failwith "Impossible")
                 in
              (match uu____31312 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____31686 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____31686 with
          | (univ_names1,binders1,tc) ->
              let uu____31760 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____31760)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____31813 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____31813 with
          | (univ_names1,binders1,tc) ->
              let uu____31887 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____31887)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____31928 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____31928 with
           | (univ_names1,binders1,typ1) ->
               let uu___377_31968 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___377_31968.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___377_31968.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___377_31968.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___377_31968.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___378_31983 = s  in
          let uu____31984 =
            let uu____31985 =
              let uu____31994 = FStar_List.map (elim_uvars env) sigs  in
              (uu____31994, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____31985  in
          {
            FStar_Syntax_Syntax.sigel = uu____31984;
            FStar_Syntax_Syntax.sigrng =
              (uu___378_31983.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___378_31983.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___378_31983.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___378_31983.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____32011 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32011 with
           | (univ_names1,uu____32035,typ1) ->
               let uu___379_32057 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_32057.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_32057.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_32057.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_32057.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____32063 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32063 with
           | (univ_names1,uu____32087,typ1) ->
               let uu___380_32109 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___380_32109.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___380_32109.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___380_32109.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___380_32109.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____32137 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____32137 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____32162 =
                            let uu____32163 =
                              let uu____32164 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____32164  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____32163
                             in
                          elim_delayed_subst_term uu____32162  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___381_32167 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___381_32167.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___381_32167.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___381_32167.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___381_32167.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___382_32168 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___382_32168.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_32168.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_32168.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_32168.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___383_32174 = s  in
          let uu____32175 =
            let uu____32176 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____32176  in
          {
            FStar_Syntax_Syntax.sigel = uu____32175;
            FStar_Syntax_Syntax.sigrng =
              (uu___383_32174.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___383_32174.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___383_32174.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___383_32174.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____32180 = elim_uvars_aux_t env us [] t  in
          (match uu____32180 with
           | (us1,uu____32204,t1) ->
               let uu___384_32226 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___384_32226.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___384_32226.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___384_32226.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___384_32226.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____32227 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____32229 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____32229 with
           | (univs1,binders,signature) ->
               let uu____32269 =
                 let uu____32274 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____32274 with
                 | (univs_opening,univs2) ->
                     let uu____32297 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____32297)
                  in
               (match uu____32269 with
                | (univs_opening,univs_closing) ->
                    let uu____32300 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____32306 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____32307 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____32306, uu____32307)  in
                    (match uu____32300 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____32333 =
                           match uu____32333 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____32351 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____32351 with
                                | (us1,t1) ->
                                    let uu____32362 =
                                      let uu____32371 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____32382 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____32371, uu____32382)  in
                                    (match uu____32362 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____32411 =
                                           let uu____32420 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____32431 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____32420, uu____32431)  in
                                         (match uu____32411 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____32461 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____32461
                                                 in
                                              let uu____32462 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____32462 with
                                               | (uu____32489,uu____32490,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____32513 =
                                                       let uu____32514 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____32514
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____32513
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____32523 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____32523 with
                           | (uu____32542,uu____32543,t1) -> t1  in
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
                             | uu____32619 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____32646 =
                               let uu____32647 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____32647.FStar_Syntax_Syntax.n  in
                             match uu____32646 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____32706 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____32739 =
                               let uu____32740 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____32740.FStar_Syntax_Syntax.n  in
                             match uu____32739 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____32763) ->
                                 let uu____32788 = destruct_action_body body
                                    in
                                 (match uu____32788 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____32837 ->
                                 let uu____32838 = destruct_action_body t  in
                                 (match uu____32838 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____32893 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____32893 with
                           | (action_univs,t) ->
                               let uu____32902 = destruct_action_typ_templ t
                                  in
                               (match uu____32902 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___385_32949 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___385_32949.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___385_32949.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___386_32951 = ed  in
                           let uu____32952 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____32953 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____32954 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____32955 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____32956 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____32957 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____32958 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____32959 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____32960 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____32961 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____32962 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____32963 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____32964 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____32965 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___386_32951.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___386_32951.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____32952;
                             FStar_Syntax_Syntax.bind_wp = uu____32953;
                             FStar_Syntax_Syntax.if_then_else = uu____32954;
                             FStar_Syntax_Syntax.ite_wp = uu____32955;
                             FStar_Syntax_Syntax.stronger = uu____32956;
                             FStar_Syntax_Syntax.close_wp = uu____32957;
                             FStar_Syntax_Syntax.assert_p = uu____32958;
                             FStar_Syntax_Syntax.assume_p = uu____32959;
                             FStar_Syntax_Syntax.null_wp = uu____32960;
                             FStar_Syntax_Syntax.trivial = uu____32961;
                             FStar_Syntax_Syntax.repr = uu____32962;
                             FStar_Syntax_Syntax.return_repr = uu____32963;
                             FStar_Syntax_Syntax.bind_repr = uu____32964;
                             FStar_Syntax_Syntax.actions = uu____32965;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___386_32951.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___387_32968 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___387_32968.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___387_32968.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___387_32968.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___387_32968.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___258_32989 =
            match uu___258_32989 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____33020 = elim_uvars_aux_t env us [] t  in
                (match uu____33020 with
                 | (us1,uu____33052,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___388_33083 = sub_eff  in
            let uu____33084 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____33087 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___388_33083.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___388_33083.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____33084;
              FStar_Syntax_Syntax.lift = uu____33087
            }  in
          let uu___389_33090 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___389_33090.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___389_33090.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___389_33090.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___389_33090.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____33100 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____33100 with
           | (univ_names1,binders1,comp1) ->
               let uu___390_33140 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___390_33140.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___390_33140.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___390_33140.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___390_33140.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____33143 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____33144 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  