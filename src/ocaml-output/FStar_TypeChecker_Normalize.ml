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
      fun uu___240_269  ->
        match uu___240_269 with
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
      let add_opt x uu___241_1503 =
        match uu___241_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___260_1523 = fs  in
          {
            beta = true;
            iota = (uu___260_1523.iota);
            zeta = (uu___260_1523.zeta);
            weak = (uu___260_1523.weak);
            hnf = (uu___260_1523.hnf);
            primops = (uu___260_1523.primops);
            do_not_unfold_pure_lets = (uu___260_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___260_1523.unfold_until);
            unfold_only = (uu___260_1523.unfold_only);
            unfold_fully = (uu___260_1523.unfold_fully);
            unfold_attr = (uu___260_1523.unfold_attr);
            unfold_tac = (uu___260_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___260_1523.pure_subterms_within_computations);
            simplify = (uu___260_1523.simplify);
            erase_universes = (uu___260_1523.erase_universes);
            allow_unbound_universes = (uu___260_1523.allow_unbound_universes);
            reify_ = (uu___260_1523.reify_);
            compress_uvars = (uu___260_1523.compress_uvars);
            no_full_norm = (uu___260_1523.no_full_norm);
            check_no_uvars = (uu___260_1523.check_no_uvars);
            unmeta = (uu___260_1523.unmeta);
            unascribe = (uu___260_1523.unascribe);
            in_full_norm_request = (uu___260_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___260_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___261_1524 = fs  in
          {
            beta = (uu___261_1524.beta);
            iota = true;
            zeta = (uu___261_1524.zeta);
            weak = (uu___261_1524.weak);
            hnf = (uu___261_1524.hnf);
            primops = (uu___261_1524.primops);
            do_not_unfold_pure_lets = (uu___261_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___261_1524.unfold_until);
            unfold_only = (uu___261_1524.unfold_only);
            unfold_fully = (uu___261_1524.unfold_fully);
            unfold_attr = (uu___261_1524.unfold_attr);
            unfold_tac = (uu___261_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___261_1524.pure_subterms_within_computations);
            simplify = (uu___261_1524.simplify);
            erase_universes = (uu___261_1524.erase_universes);
            allow_unbound_universes = (uu___261_1524.allow_unbound_universes);
            reify_ = (uu___261_1524.reify_);
            compress_uvars = (uu___261_1524.compress_uvars);
            no_full_norm = (uu___261_1524.no_full_norm);
            check_no_uvars = (uu___261_1524.check_no_uvars);
            unmeta = (uu___261_1524.unmeta);
            unascribe = (uu___261_1524.unascribe);
            in_full_norm_request = (uu___261_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___261_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___262_1525 = fs  in
          {
            beta = (uu___262_1525.beta);
            iota = (uu___262_1525.iota);
            zeta = true;
            weak = (uu___262_1525.weak);
            hnf = (uu___262_1525.hnf);
            primops = (uu___262_1525.primops);
            do_not_unfold_pure_lets = (uu___262_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___262_1525.unfold_until);
            unfold_only = (uu___262_1525.unfold_only);
            unfold_fully = (uu___262_1525.unfold_fully);
            unfold_attr = (uu___262_1525.unfold_attr);
            unfold_tac = (uu___262_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___262_1525.pure_subterms_within_computations);
            simplify = (uu___262_1525.simplify);
            erase_universes = (uu___262_1525.erase_universes);
            allow_unbound_universes = (uu___262_1525.allow_unbound_universes);
            reify_ = (uu___262_1525.reify_);
            compress_uvars = (uu___262_1525.compress_uvars);
            no_full_norm = (uu___262_1525.no_full_norm);
            check_no_uvars = (uu___262_1525.check_no_uvars);
            unmeta = (uu___262_1525.unmeta);
            unascribe = (uu___262_1525.unascribe);
            in_full_norm_request = (uu___262_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___262_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___263_1526 = fs  in
          {
            beta = false;
            iota = (uu___263_1526.iota);
            zeta = (uu___263_1526.zeta);
            weak = (uu___263_1526.weak);
            hnf = (uu___263_1526.hnf);
            primops = (uu___263_1526.primops);
            do_not_unfold_pure_lets = (uu___263_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___263_1526.unfold_until);
            unfold_only = (uu___263_1526.unfold_only);
            unfold_fully = (uu___263_1526.unfold_fully);
            unfold_attr = (uu___263_1526.unfold_attr);
            unfold_tac = (uu___263_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___263_1526.pure_subterms_within_computations);
            simplify = (uu___263_1526.simplify);
            erase_universes = (uu___263_1526.erase_universes);
            allow_unbound_universes = (uu___263_1526.allow_unbound_universes);
            reify_ = (uu___263_1526.reify_);
            compress_uvars = (uu___263_1526.compress_uvars);
            no_full_norm = (uu___263_1526.no_full_norm);
            check_no_uvars = (uu___263_1526.check_no_uvars);
            unmeta = (uu___263_1526.unmeta);
            unascribe = (uu___263_1526.unascribe);
            in_full_norm_request = (uu___263_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___263_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___264_1527 = fs  in
          {
            beta = (uu___264_1527.beta);
            iota = false;
            zeta = (uu___264_1527.zeta);
            weak = (uu___264_1527.weak);
            hnf = (uu___264_1527.hnf);
            primops = (uu___264_1527.primops);
            do_not_unfold_pure_lets = (uu___264_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___264_1527.unfold_until);
            unfold_only = (uu___264_1527.unfold_only);
            unfold_fully = (uu___264_1527.unfold_fully);
            unfold_attr = (uu___264_1527.unfold_attr);
            unfold_tac = (uu___264_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___264_1527.pure_subterms_within_computations);
            simplify = (uu___264_1527.simplify);
            erase_universes = (uu___264_1527.erase_universes);
            allow_unbound_universes = (uu___264_1527.allow_unbound_universes);
            reify_ = (uu___264_1527.reify_);
            compress_uvars = (uu___264_1527.compress_uvars);
            no_full_norm = (uu___264_1527.no_full_norm);
            check_no_uvars = (uu___264_1527.check_no_uvars);
            unmeta = (uu___264_1527.unmeta);
            unascribe = (uu___264_1527.unascribe);
            in_full_norm_request = (uu___264_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___264_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___265_1528 = fs  in
          {
            beta = (uu___265_1528.beta);
            iota = (uu___265_1528.iota);
            zeta = false;
            weak = (uu___265_1528.weak);
            hnf = (uu___265_1528.hnf);
            primops = (uu___265_1528.primops);
            do_not_unfold_pure_lets = (uu___265_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___265_1528.unfold_until);
            unfold_only = (uu___265_1528.unfold_only);
            unfold_fully = (uu___265_1528.unfold_fully);
            unfold_attr = (uu___265_1528.unfold_attr);
            unfold_tac = (uu___265_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_1528.pure_subterms_within_computations);
            simplify = (uu___265_1528.simplify);
            erase_universes = (uu___265_1528.erase_universes);
            allow_unbound_universes = (uu___265_1528.allow_unbound_universes);
            reify_ = (uu___265_1528.reify_);
            compress_uvars = (uu___265_1528.compress_uvars);
            no_full_norm = (uu___265_1528.no_full_norm);
            check_no_uvars = (uu___265_1528.check_no_uvars);
            unmeta = (uu___265_1528.unmeta);
            unascribe = (uu___265_1528.unascribe);
            in_full_norm_request = (uu___265_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___266_1530 = fs  in
          {
            beta = (uu___266_1530.beta);
            iota = (uu___266_1530.iota);
            zeta = (uu___266_1530.zeta);
            weak = true;
            hnf = (uu___266_1530.hnf);
            primops = (uu___266_1530.primops);
            do_not_unfold_pure_lets = (uu___266_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___266_1530.unfold_until);
            unfold_only = (uu___266_1530.unfold_only);
            unfold_fully = (uu___266_1530.unfold_fully);
            unfold_attr = (uu___266_1530.unfold_attr);
            unfold_tac = (uu___266_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___266_1530.pure_subterms_within_computations);
            simplify = (uu___266_1530.simplify);
            erase_universes = (uu___266_1530.erase_universes);
            allow_unbound_universes = (uu___266_1530.allow_unbound_universes);
            reify_ = (uu___266_1530.reify_);
            compress_uvars = (uu___266_1530.compress_uvars);
            no_full_norm = (uu___266_1530.no_full_norm);
            check_no_uvars = (uu___266_1530.check_no_uvars);
            unmeta = (uu___266_1530.unmeta);
            unascribe = (uu___266_1530.unascribe);
            in_full_norm_request = (uu___266_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___266_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___267_1531 = fs  in
          {
            beta = (uu___267_1531.beta);
            iota = (uu___267_1531.iota);
            zeta = (uu___267_1531.zeta);
            weak = (uu___267_1531.weak);
            hnf = true;
            primops = (uu___267_1531.primops);
            do_not_unfold_pure_lets = (uu___267_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___267_1531.unfold_until);
            unfold_only = (uu___267_1531.unfold_only);
            unfold_fully = (uu___267_1531.unfold_fully);
            unfold_attr = (uu___267_1531.unfold_attr);
            unfold_tac = (uu___267_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___267_1531.pure_subterms_within_computations);
            simplify = (uu___267_1531.simplify);
            erase_universes = (uu___267_1531.erase_universes);
            allow_unbound_universes = (uu___267_1531.allow_unbound_universes);
            reify_ = (uu___267_1531.reify_);
            compress_uvars = (uu___267_1531.compress_uvars);
            no_full_norm = (uu___267_1531.no_full_norm);
            check_no_uvars = (uu___267_1531.check_no_uvars);
            unmeta = (uu___267_1531.unmeta);
            unascribe = (uu___267_1531.unascribe);
            in_full_norm_request = (uu___267_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___267_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___268_1532 = fs  in
          {
            beta = (uu___268_1532.beta);
            iota = (uu___268_1532.iota);
            zeta = (uu___268_1532.zeta);
            weak = (uu___268_1532.weak);
            hnf = (uu___268_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___268_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___268_1532.unfold_until);
            unfold_only = (uu___268_1532.unfold_only);
            unfold_fully = (uu___268_1532.unfold_fully);
            unfold_attr = (uu___268_1532.unfold_attr);
            unfold_tac = (uu___268_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___268_1532.pure_subterms_within_computations);
            simplify = (uu___268_1532.simplify);
            erase_universes = (uu___268_1532.erase_universes);
            allow_unbound_universes = (uu___268_1532.allow_unbound_universes);
            reify_ = (uu___268_1532.reify_);
            compress_uvars = (uu___268_1532.compress_uvars);
            no_full_norm = (uu___268_1532.no_full_norm);
            check_no_uvars = (uu___268_1532.check_no_uvars);
            unmeta = (uu___268_1532.unmeta);
            unascribe = (uu___268_1532.unascribe);
            in_full_norm_request = (uu___268_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___268_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___269_1533 = fs  in
          {
            beta = (uu___269_1533.beta);
            iota = (uu___269_1533.iota);
            zeta = (uu___269_1533.zeta);
            weak = (uu___269_1533.weak);
            hnf = (uu___269_1533.hnf);
            primops = (uu___269_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___269_1533.unfold_until);
            unfold_only = (uu___269_1533.unfold_only);
            unfold_fully = (uu___269_1533.unfold_fully);
            unfold_attr = (uu___269_1533.unfold_attr);
            unfold_tac = (uu___269_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___269_1533.pure_subterms_within_computations);
            simplify = (uu___269_1533.simplify);
            erase_universes = (uu___269_1533.erase_universes);
            allow_unbound_universes = (uu___269_1533.allow_unbound_universes);
            reify_ = (uu___269_1533.reify_);
            compress_uvars = (uu___269_1533.compress_uvars);
            no_full_norm = (uu___269_1533.no_full_norm);
            check_no_uvars = (uu___269_1533.check_no_uvars);
            unmeta = (uu___269_1533.unmeta);
            unascribe = (uu___269_1533.unascribe);
            in_full_norm_request = (uu___269_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___269_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___270_1535 = fs  in
          {
            beta = (uu___270_1535.beta);
            iota = (uu___270_1535.iota);
            zeta = (uu___270_1535.zeta);
            weak = (uu___270_1535.weak);
            hnf = (uu___270_1535.hnf);
            primops = (uu___270_1535.primops);
            do_not_unfold_pure_lets = (uu___270_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___270_1535.unfold_only);
            unfold_fully = (uu___270_1535.unfold_fully);
            unfold_attr = (uu___270_1535.unfold_attr);
            unfold_tac = (uu___270_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___270_1535.pure_subterms_within_computations);
            simplify = (uu___270_1535.simplify);
            erase_universes = (uu___270_1535.erase_universes);
            allow_unbound_universes = (uu___270_1535.allow_unbound_universes);
            reify_ = (uu___270_1535.reify_);
            compress_uvars = (uu___270_1535.compress_uvars);
            no_full_norm = (uu___270_1535.no_full_norm);
            check_no_uvars = (uu___270_1535.check_no_uvars);
            unmeta = (uu___270_1535.unmeta);
            unascribe = (uu___270_1535.unascribe);
            in_full_norm_request = (uu___270_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___270_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___271_1539 = fs  in
          {
            beta = (uu___271_1539.beta);
            iota = (uu___271_1539.iota);
            zeta = (uu___271_1539.zeta);
            weak = (uu___271_1539.weak);
            hnf = (uu___271_1539.hnf);
            primops = (uu___271_1539.primops);
            do_not_unfold_pure_lets = (uu___271_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___271_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___271_1539.unfold_fully);
            unfold_attr = (uu___271_1539.unfold_attr);
            unfold_tac = (uu___271_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___271_1539.pure_subterms_within_computations);
            simplify = (uu___271_1539.simplify);
            erase_universes = (uu___271_1539.erase_universes);
            allow_unbound_universes = (uu___271_1539.allow_unbound_universes);
            reify_ = (uu___271_1539.reify_);
            compress_uvars = (uu___271_1539.compress_uvars);
            no_full_norm = (uu___271_1539.no_full_norm);
            check_no_uvars = (uu___271_1539.check_no_uvars);
            unmeta = (uu___271_1539.unmeta);
            unascribe = (uu___271_1539.unascribe);
            in_full_norm_request = (uu___271_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___271_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___272_1545 = fs  in
          {
            beta = (uu___272_1545.beta);
            iota = (uu___272_1545.iota);
            zeta = (uu___272_1545.zeta);
            weak = (uu___272_1545.weak);
            hnf = (uu___272_1545.hnf);
            primops = (uu___272_1545.primops);
            do_not_unfold_pure_lets = (uu___272_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___272_1545.unfold_until);
            unfold_only = (uu___272_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___272_1545.unfold_attr);
            unfold_tac = (uu___272_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___272_1545.pure_subterms_within_computations);
            simplify = (uu___272_1545.simplify);
            erase_universes = (uu___272_1545.erase_universes);
            allow_unbound_universes = (uu___272_1545.allow_unbound_universes);
            reify_ = (uu___272_1545.reify_);
            compress_uvars = (uu___272_1545.compress_uvars);
            no_full_norm = (uu___272_1545.no_full_norm);
            check_no_uvars = (uu___272_1545.check_no_uvars);
            unmeta = (uu___272_1545.unmeta);
            unascribe = (uu___272_1545.unascribe);
            in_full_norm_request = (uu___272_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___272_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___273_1549 = fs  in
          {
            beta = (uu___273_1549.beta);
            iota = (uu___273_1549.iota);
            zeta = (uu___273_1549.zeta);
            weak = (uu___273_1549.weak);
            hnf = (uu___273_1549.hnf);
            primops = (uu___273_1549.primops);
            do_not_unfold_pure_lets = (uu___273_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___273_1549.unfold_until);
            unfold_only = (uu___273_1549.unfold_only);
            unfold_fully = (uu___273_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___273_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___273_1549.pure_subterms_within_computations);
            simplify = (uu___273_1549.simplify);
            erase_universes = (uu___273_1549.erase_universes);
            allow_unbound_universes = (uu___273_1549.allow_unbound_universes);
            reify_ = (uu___273_1549.reify_);
            compress_uvars = (uu___273_1549.compress_uvars);
            no_full_norm = (uu___273_1549.no_full_norm);
            check_no_uvars = (uu___273_1549.check_no_uvars);
            unmeta = (uu___273_1549.unmeta);
            unascribe = (uu___273_1549.unascribe);
            in_full_norm_request = (uu___273_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___273_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___274_1550 = fs  in
          {
            beta = (uu___274_1550.beta);
            iota = (uu___274_1550.iota);
            zeta = (uu___274_1550.zeta);
            weak = (uu___274_1550.weak);
            hnf = (uu___274_1550.hnf);
            primops = (uu___274_1550.primops);
            do_not_unfold_pure_lets = (uu___274_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___274_1550.unfold_until);
            unfold_only = (uu___274_1550.unfold_only);
            unfold_fully = (uu___274_1550.unfold_fully);
            unfold_attr = (uu___274_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___274_1550.pure_subterms_within_computations);
            simplify = (uu___274_1550.simplify);
            erase_universes = (uu___274_1550.erase_universes);
            allow_unbound_universes = (uu___274_1550.allow_unbound_universes);
            reify_ = (uu___274_1550.reify_);
            compress_uvars = (uu___274_1550.compress_uvars);
            no_full_norm = (uu___274_1550.no_full_norm);
            check_no_uvars = (uu___274_1550.check_no_uvars);
            unmeta = (uu___274_1550.unmeta);
            unascribe = (uu___274_1550.unascribe);
            in_full_norm_request = (uu___274_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___274_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___275_1551 = fs  in
          {
            beta = (uu___275_1551.beta);
            iota = (uu___275_1551.iota);
            zeta = (uu___275_1551.zeta);
            weak = (uu___275_1551.weak);
            hnf = (uu___275_1551.hnf);
            primops = (uu___275_1551.primops);
            do_not_unfold_pure_lets = (uu___275_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___275_1551.unfold_until);
            unfold_only = (uu___275_1551.unfold_only);
            unfold_fully = (uu___275_1551.unfold_fully);
            unfold_attr = (uu___275_1551.unfold_attr);
            unfold_tac = (uu___275_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___275_1551.simplify);
            erase_universes = (uu___275_1551.erase_universes);
            allow_unbound_universes = (uu___275_1551.allow_unbound_universes);
            reify_ = (uu___275_1551.reify_);
            compress_uvars = (uu___275_1551.compress_uvars);
            no_full_norm = (uu___275_1551.no_full_norm);
            check_no_uvars = (uu___275_1551.check_no_uvars);
            unmeta = (uu___275_1551.unmeta);
            unascribe = (uu___275_1551.unascribe);
            in_full_norm_request = (uu___275_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___275_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___276_1552 = fs  in
          {
            beta = (uu___276_1552.beta);
            iota = (uu___276_1552.iota);
            zeta = (uu___276_1552.zeta);
            weak = (uu___276_1552.weak);
            hnf = (uu___276_1552.hnf);
            primops = (uu___276_1552.primops);
            do_not_unfold_pure_lets = (uu___276_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___276_1552.unfold_until);
            unfold_only = (uu___276_1552.unfold_only);
            unfold_fully = (uu___276_1552.unfold_fully);
            unfold_attr = (uu___276_1552.unfold_attr);
            unfold_tac = (uu___276_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___276_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___276_1552.erase_universes);
            allow_unbound_universes = (uu___276_1552.allow_unbound_universes);
            reify_ = (uu___276_1552.reify_);
            compress_uvars = (uu___276_1552.compress_uvars);
            no_full_norm = (uu___276_1552.no_full_norm);
            check_no_uvars = (uu___276_1552.check_no_uvars);
            unmeta = (uu___276_1552.unmeta);
            unascribe = (uu___276_1552.unascribe);
            in_full_norm_request = (uu___276_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___276_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___277_1553 = fs  in
          {
            beta = (uu___277_1553.beta);
            iota = (uu___277_1553.iota);
            zeta = (uu___277_1553.zeta);
            weak = (uu___277_1553.weak);
            hnf = (uu___277_1553.hnf);
            primops = (uu___277_1553.primops);
            do_not_unfold_pure_lets = (uu___277_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___277_1553.unfold_until);
            unfold_only = (uu___277_1553.unfold_only);
            unfold_fully = (uu___277_1553.unfold_fully);
            unfold_attr = (uu___277_1553.unfold_attr);
            unfold_tac = (uu___277_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___277_1553.pure_subterms_within_computations);
            simplify = (uu___277_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___277_1553.allow_unbound_universes);
            reify_ = (uu___277_1553.reify_);
            compress_uvars = (uu___277_1553.compress_uvars);
            no_full_norm = (uu___277_1553.no_full_norm);
            check_no_uvars = (uu___277_1553.check_no_uvars);
            unmeta = (uu___277_1553.unmeta);
            unascribe = (uu___277_1553.unascribe);
            in_full_norm_request = (uu___277_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___277_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___278_1554 = fs  in
          {
            beta = (uu___278_1554.beta);
            iota = (uu___278_1554.iota);
            zeta = (uu___278_1554.zeta);
            weak = (uu___278_1554.weak);
            hnf = (uu___278_1554.hnf);
            primops = (uu___278_1554.primops);
            do_not_unfold_pure_lets = (uu___278_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___278_1554.unfold_until);
            unfold_only = (uu___278_1554.unfold_only);
            unfold_fully = (uu___278_1554.unfold_fully);
            unfold_attr = (uu___278_1554.unfold_attr);
            unfold_tac = (uu___278_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___278_1554.pure_subterms_within_computations);
            simplify = (uu___278_1554.simplify);
            erase_universes = (uu___278_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___278_1554.reify_);
            compress_uvars = (uu___278_1554.compress_uvars);
            no_full_norm = (uu___278_1554.no_full_norm);
            check_no_uvars = (uu___278_1554.check_no_uvars);
            unmeta = (uu___278_1554.unmeta);
            unascribe = (uu___278_1554.unascribe);
            in_full_norm_request = (uu___278_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___278_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___279_1555 = fs  in
          {
            beta = (uu___279_1555.beta);
            iota = (uu___279_1555.iota);
            zeta = (uu___279_1555.zeta);
            weak = (uu___279_1555.weak);
            hnf = (uu___279_1555.hnf);
            primops = (uu___279_1555.primops);
            do_not_unfold_pure_lets = (uu___279_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___279_1555.unfold_until);
            unfold_only = (uu___279_1555.unfold_only);
            unfold_fully = (uu___279_1555.unfold_fully);
            unfold_attr = (uu___279_1555.unfold_attr);
            unfold_tac = (uu___279_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___279_1555.pure_subterms_within_computations);
            simplify = (uu___279_1555.simplify);
            erase_universes = (uu___279_1555.erase_universes);
            allow_unbound_universes = (uu___279_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___279_1555.compress_uvars);
            no_full_norm = (uu___279_1555.no_full_norm);
            check_no_uvars = (uu___279_1555.check_no_uvars);
            unmeta = (uu___279_1555.unmeta);
            unascribe = (uu___279_1555.unascribe);
            in_full_norm_request = (uu___279_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___279_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___280_1556 = fs  in
          {
            beta = (uu___280_1556.beta);
            iota = (uu___280_1556.iota);
            zeta = (uu___280_1556.zeta);
            weak = (uu___280_1556.weak);
            hnf = (uu___280_1556.hnf);
            primops = (uu___280_1556.primops);
            do_not_unfold_pure_lets = (uu___280_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___280_1556.unfold_until);
            unfold_only = (uu___280_1556.unfold_only);
            unfold_fully = (uu___280_1556.unfold_fully);
            unfold_attr = (uu___280_1556.unfold_attr);
            unfold_tac = (uu___280_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___280_1556.pure_subterms_within_computations);
            simplify = (uu___280_1556.simplify);
            erase_universes = (uu___280_1556.erase_universes);
            allow_unbound_universes = (uu___280_1556.allow_unbound_universes);
            reify_ = (uu___280_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___280_1556.no_full_norm);
            check_no_uvars = (uu___280_1556.check_no_uvars);
            unmeta = (uu___280_1556.unmeta);
            unascribe = (uu___280_1556.unascribe);
            in_full_norm_request = (uu___280_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___280_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___281_1557 = fs  in
          {
            beta = (uu___281_1557.beta);
            iota = (uu___281_1557.iota);
            zeta = (uu___281_1557.zeta);
            weak = (uu___281_1557.weak);
            hnf = (uu___281_1557.hnf);
            primops = (uu___281_1557.primops);
            do_not_unfold_pure_lets = (uu___281_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___281_1557.unfold_until);
            unfold_only = (uu___281_1557.unfold_only);
            unfold_fully = (uu___281_1557.unfold_fully);
            unfold_attr = (uu___281_1557.unfold_attr);
            unfold_tac = (uu___281_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___281_1557.pure_subterms_within_computations);
            simplify = (uu___281_1557.simplify);
            erase_universes = (uu___281_1557.erase_universes);
            allow_unbound_universes = (uu___281_1557.allow_unbound_universes);
            reify_ = (uu___281_1557.reify_);
            compress_uvars = (uu___281_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___281_1557.check_no_uvars);
            unmeta = (uu___281_1557.unmeta);
            unascribe = (uu___281_1557.unascribe);
            in_full_norm_request = (uu___281_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___281_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___282_1558 = fs  in
          {
            beta = (uu___282_1558.beta);
            iota = (uu___282_1558.iota);
            zeta = (uu___282_1558.zeta);
            weak = (uu___282_1558.weak);
            hnf = (uu___282_1558.hnf);
            primops = (uu___282_1558.primops);
            do_not_unfold_pure_lets = (uu___282_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___282_1558.unfold_until);
            unfold_only = (uu___282_1558.unfold_only);
            unfold_fully = (uu___282_1558.unfold_fully);
            unfold_attr = (uu___282_1558.unfold_attr);
            unfold_tac = (uu___282_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___282_1558.pure_subterms_within_computations);
            simplify = (uu___282_1558.simplify);
            erase_universes = (uu___282_1558.erase_universes);
            allow_unbound_universes = (uu___282_1558.allow_unbound_universes);
            reify_ = (uu___282_1558.reify_);
            compress_uvars = (uu___282_1558.compress_uvars);
            no_full_norm = (uu___282_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___282_1558.unmeta);
            unascribe = (uu___282_1558.unascribe);
            in_full_norm_request = (uu___282_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___282_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___283_1559 = fs  in
          {
            beta = (uu___283_1559.beta);
            iota = (uu___283_1559.iota);
            zeta = (uu___283_1559.zeta);
            weak = (uu___283_1559.weak);
            hnf = (uu___283_1559.hnf);
            primops = (uu___283_1559.primops);
            do_not_unfold_pure_lets = (uu___283_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___283_1559.unfold_until);
            unfold_only = (uu___283_1559.unfold_only);
            unfold_fully = (uu___283_1559.unfold_fully);
            unfold_attr = (uu___283_1559.unfold_attr);
            unfold_tac = (uu___283_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___283_1559.pure_subterms_within_computations);
            simplify = (uu___283_1559.simplify);
            erase_universes = (uu___283_1559.erase_universes);
            allow_unbound_universes = (uu___283_1559.allow_unbound_universes);
            reify_ = (uu___283_1559.reify_);
            compress_uvars = (uu___283_1559.compress_uvars);
            no_full_norm = (uu___283_1559.no_full_norm);
            check_no_uvars = (uu___283_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___283_1559.unascribe);
            in_full_norm_request = (uu___283_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___283_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___284_1560 = fs  in
          {
            beta = (uu___284_1560.beta);
            iota = (uu___284_1560.iota);
            zeta = (uu___284_1560.zeta);
            weak = (uu___284_1560.weak);
            hnf = (uu___284_1560.hnf);
            primops = (uu___284_1560.primops);
            do_not_unfold_pure_lets = (uu___284_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___284_1560.unfold_until);
            unfold_only = (uu___284_1560.unfold_only);
            unfold_fully = (uu___284_1560.unfold_fully);
            unfold_attr = (uu___284_1560.unfold_attr);
            unfold_tac = (uu___284_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___284_1560.pure_subterms_within_computations);
            simplify = (uu___284_1560.simplify);
            erase_universes = (uu___284_1560.erase_universes);
            allow_unbound_universes = (uu___284_1560.allow_unbound_universes);
            reify_ = (uu___284_1560.reify_);
            compress_uvars = (uu___284_1560.compress_uvars);
            no_full_norm = (uu___284_1560.no_full_norm);
            check_no_uvars = (uu___284_1560.check_no_uvars);
            unmeta = (uu___284_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___284_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___284_1560.weakly_reduce_scrutinee)
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
  fun uu___242_3251  ->
    match uu___242_3251 with
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
  fun uu___243_3313  ->
    match uu___243_3313 with
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
  fun uu___244_3451  ->
    match uu___244_3451 with | [] -> true | uu____3454 -> false
  
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
                                      (fun uu___245_4054  ->
                                         match uu___245_4054 with
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
                                                 (let uu___289_4078 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___289_4078.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___289_4078.FStar_Syntax_Syntax.sort)
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
                         let uu___290_4090 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___290_4090.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___290_4090.FStar_Syntax_Syntax.vars)
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
                           let uu___291_4129 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___291_4129.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___291_4129.FStar_Syntax_Syntax.index);
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
                             (let uu___292_4929 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___292_4929.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___292_4929.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4913))
                       in
                    (match uu____4883 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___293_4947 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___293_4947.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___293_4947.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___293_4947.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___293_4947.FStar_Syntax_Syntax.lbpos)
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
                             (let uu___294_5085 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___294_5085.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___294_5085.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___295_5086 = lb  in
                      let uu____5087 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___295_5086.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___295_5086.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5087;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___295_5086.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___295_5086.FStar_Syntax_Syntax.lbpos)
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
                      let uu___296_5336 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___296_5336.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___296_5336.FStar_Syntax_Syntax.vars)
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
                                ((let uu___297_5922 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___297_5922.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___298_5941 = x  in
                             let uu____5942 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___298_5941.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___298_5941.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5942
                             }  in
                           ((let uu___299_5956 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___299_5956.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___300_5967 = x  in
                             let uu____5968 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___300_5967.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___300_5967.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5968
                             }  in
                           ((let uu___301_5982 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___301_5982.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___302_5998 = x  in
                             let uu____5999 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___302_5998.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___302_5998.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5999
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___303_6016 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___303_6016.FStar_Syntax_Syntax.p)
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
                          let uu___304_6676 = b  in
                          let uu____6677 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___304_6676.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___304_6676.FStar_Syntax_Syntax.index);
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
                        (fun uu___246_6934  ->
                           match uu___246_6934 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6938 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6938
                           | f -> f))
                    in
                 let uu____6942 =
                   let uu___305_6943 = c1  in
                   let uu____6944 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6944;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___305_6943.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___247_6954  ->
            match uu___247_6954 with
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
                   (fun uu___248_6976  ->
                      match uu___248_6976 with
                      | FStar_Syntax_Syntax.DECREASES uu____6977 -> false
                      | uu____6980 -> true))
               in
            let rc1 =
              let uu___306_6982 = rc  in
              let uu____6983 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___306_6982.FStar_Syntax_Syntax.residual_effect);
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
  let string_split' psc args =
    match args with
    | a1::a2::[] ->
        let uu____8163 = arg_as_list FStar_Syntax_Embeddings.e_char a1  in
        (match uu____8163 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8179 = arg_as_string a2  in
             (match uu____8179 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8188 =
                    let uu____8189 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    FStar_Syntax_Embeddings.embed uu____8189 psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____8188
              | uu____8196 -> FStar_Pervasives_Native.None)
         | uu____8199 -> FStar_Pervasives_Native.None)
    | uu____8205 -> FStar_Pervasives_Native.None  in
  let string_substring' psc args =
    match args with
    | a1::a2::a3::[] ->
        let uu____8236 =
          let uu____8249 = arg_as_string a1  in
          let uu____8252 = arg_as_int a2  in
          let uu____8255 = arg_as_int a3  in
          (uu____8249, uu____8252, uu____8255)  in
        (match uu____8236 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____8286 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string psc.psc_range r
                   in
                FStar_Pervasives_Native.Some uu____8286
              with | uu____8292 -> FStar_Pervasives_Native.None)
         | uu____8293 -> FStar_Pervasives_Native.None)
    | uu____8306 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____8320 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____8320
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8357 =
          let uu____8378 = arg_as_string fn  in
          let uu____8381 = arg_as_int from_line  in
          let uu____8384 = arg_as_int from_col  in
          let uu____8387 = arg_as_int to_line  in
          let uu____8390 = arg_as_int to_col  in
          (uu____8378, uu____8381, uu____8384, uu____8387, uu____8390)  in
        (match uu____8357 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8421 =
                 let uu____8422 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8423 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8422 uu____8423  in
               let uu____8424 =
                 let uu____8425 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8426 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8425 uu____8426  in
               FStar_Range.mk_range fn1 uu____8421 uu____8424  in
             let uu____8427 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8427
         | uu____8428 -> FStar_Pervasives_Native.None)
    | uu____8449 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8482)::(a1,uu____8484)::(a2,uu____8486)::[] ->
        let uu____8543 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8543 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8548 -> FStar_Pervasives_Native.None)
    | uu____8549 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8584)::[] ->
        let uu____8601 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8601 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8607 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8607
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8608 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8636 =
      let uu____8653 =
        let uu____8670 =
          let uu____8687 =
            let uu____8704 =
              let uu____8721 =
                let uu____8738 =
                  let uu____8755 =
                    let uu____8772 =
                      let uu____8789 =
                        let uu____8806 =
                          let uu____8823 =
                            let uu____8840 =
                              let uu____8857 =
                                let uu____8874 =
                                  let uu____8891 =
                                    let uu____8908 =
                                      let uu____8925 =
                                        let uu____8942 =
                                          let uu____8959 =
                                            let uu____8976 =
                                              let uu____8993 =
                                                let uu____9008 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____9008,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____9017 =
                                                let uu____9034 =
                                                  let uu____9049 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____9049,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____9062 =
                                                  let uu____9079 =
                                                    let uu____9094 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____9094,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____9103 =
                                                    let uu____9120 =
                                                      let uu____9135 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "String";
                                                          "split"]
                                                         in
                                                      (uu____9135,
                                                        (Prims.parse_int "2"),
                                                        string_split')
                                                       in
                                                    let uu____9144 =
                                                      let uu____9161 =
                                                        let uu____9176 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "String";
                                                            "substring"]
                                                           in
                                                        (uu____9176,
                                                          (Prims.parse_int "3"),
                                                          string_substring')
                                                         in
                                                      let uu____9185 =
                                                        let uu____9202 =
                                                          let uu____9217 =
                                                            FStar_Parser_Const.p2l
                                                              ["Prims";
                                                              "mk_range"]
                                                             in
                                                          (uu____9217,
                                                            (Prims.parse_int "5"),
                                                            mk_range1)
                                                           in
                                                        [uu____9202]  in
                                                      uu____9161 ::
                                                        uu____9185
                                                       in
                                                    uu____9120 :: uu____9144
                                                     in
                                                  uu____9079 :: uu____9103
                                                   in
                                                uu____9034 :: uu____9062  in
                                              uu____8993 :: uu____9017  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8976
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8959
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8942
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8925
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8908
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____9465 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____9465 y)))
                                    :: uu____8891
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8874
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8857
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8840
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8823
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8806
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8789
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9660 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9660)))
                      :: uu____8772
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9690 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9690)))
                    :: uu____8755
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9720 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9720)))
                  :: uu____8738
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9750 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9750)))
                :: uu____8721
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8704
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8687
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8670
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8653
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8636
     in
  let weak_ops =
    let uu____9905 =
      let uu____9920 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9920, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9905]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____10000 =
        let uu____10005 =
          let uu____10006 = FStar_Syntax_Syntax.as_arg c  in [uu____10006]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____10005  in
      uu____10000 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10086 =
                let uu____10101 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____10101, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____10123  ->
                          fun uu____10124  ->
                            match (uu____10123, uu____10124) with
                            | ((int_to_t1,x),(uu____10143,y)) ->
                                let uu____10153 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded r int_to_t1 uu____10153)))
                 in
              let uu____10154 =
                let uu____10171 =
                  let uu____10186 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  (uu____10186, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10208  ->
                            fun uu____10209  ->
                              match (uu____10208, uu____10209) with
                              | ((int_to_t1,x),(uu____10228,y)) ->
                                  let uu____10238 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10238)))
                   in
                let uu____10239 =
                  let uu____10256 =
                    let uu____10271 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____10271, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____10293  ->
                              fun uu____10294  ->
                                match (uu____10293, uu____10294) with
                                | ((int_to_t1,x),(uu____10313,y)) ->
                                    let uu____10323 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____10323)))
                     in
                  let uu____10324 =
                    let uu____10341 =
                      let uu____10356 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____10356, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____10374  ->
                                match uu____10374 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____10341]  in
                  uu____10256 :: uu____10324  in
                uu____10171 :: uu____10239  in
              uu____10086 :: uu____10154))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10504 =
                let uu____10519 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____10519, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____10541  ->
                          fun uu____10542  ->
                            match (uu____10541, uu____10542) with
                            | ((int_to_t1,x),(uu____10561,y)) ->
                                let uu____10571 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded r int_to_t1 uu____10571)))
                 in
              let uu____10572 =
                let uu____10589 =
                  let uu____10604 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10604, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10626  ->
                            fun uu____10627  ->
                              match (uu____10626, uu____10627) with
                              | ((int_to_t1,x),(uu____10646,y)) ->
                                  let uu____10656 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10656)))
                   in
                [uu____10589]  in
              uu____10504 :: uu____10572))
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
    | (_typ,uu____10786)::(a1,uu____10788)::(a2,uu____10790)::[] ->
        let uu____10847 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10847 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___309_10851 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___309_10851.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___309_10851.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___310_10853 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___310_10853.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___310_10853.FStar_Syntax_Syntax.vars)
                })
         | uu____10854 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10856)::uu____10857::(a1,uu____10859)::(a2,uu____10861)::[]
        ->
        let uu____10934 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10934 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___309_10938 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___309_10938.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___309_10938.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___310_10940 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___310_10940.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___310_10940.FStar_Syntax_Syntax.vars)
                })
         | uu____10941 -> FStar_Pervasives_Native.None)
    | uu____10942 -> failwith "Unexpected number of arguments"  in
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
    let uu____10996 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10996 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____11048 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11048) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____11110  ->
           fun subst1  ->
             match uu____11110 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____11151,uu____11152)) ->
                      let uu____11211 = b  in
                      (match uu____11211 with
                       | (bv,uu____11219) ->
                           let uu____11220 =
                             let uu____11221 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____11221  in
                           if uu____11220
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____11226 = unembed_binder term1  in
                              match uu____11226 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____11233 =
                                      let uu___311_11234 = bv  in
                                      let uu____11235 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___311_11234.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___311_11234.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____11235
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____11233
                                     in
                                  let b_for_x =
                                    let uu____11241 =
                                      let uu____11248 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____11248)
                                       in
                                    FStar_Syntax_Syntax.NT uu____11241  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___249_11264  ->
                                         match uu___249_11264 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____11265,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____11267;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____11268;_})
                                             ->
                                             let uu____11273 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____11273
                                         | uu____11274 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____11275 -> subst1)) env []
  
let reduce_primops :
  'Auu____11298 'Auu____11299 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11298) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11299 ->
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
            (let uu____11347 = FStar_Syntax_Util.head_and_args tm  in
             match uu____11347 with
             | (head1,args) ->
                 let uu____11392 =
                   let uu____11393 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11393.FStar_Syntax_Syntax.n  in
                 (match uu____11392 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____11399 = find_prim_step cfg fv  in
                      (match uu____11399 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____11427  ->
                                   let uu____11428 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____11429 =
                                     FStar_Util.string_of_int l  in
                                   let uu____11436 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____11428 uu____11429 uu____11436);
                              tm)
                           else
                             (let uu____11438 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____11438 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____11575  ->
                                        let uu____11576 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____11576);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____11579  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____11581 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____11581 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____11589  ->
                                              let uu____11590 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____11590);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____11596  ->
                                              let uu____11597 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____11598 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____11597 uu____11598);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____11599 ->
                           (log_primops cfg
                              (fun uu____11603  ->
                                 let uu____11604 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____11604);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11608  ->
                            let uu____11609 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11609);
                       (match args with
                        | (a1,uu____11613)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____11638 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11652  ->
                            let uu____11653 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11653);
                       (match args with
                        | (t,uu____11657)::(r,uu____11659)::[] ->
                            let uu____11700 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11700 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11706 -> tm))
                  | uu____11717 -> tm))
  
let reduce_equality :
  'Auu____11728 'Auu____11729 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11728) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11729 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___312_11775 = cfg  in
         {
           steps =
             (let uu___313_11778 = default_steps  in
              {
                beta = (uu___313_11778.beta);
                iota = (uu___313_11778.iota);
                zeta = (uu___313_11778.zeta);
                weak = (uu___313_11778.weak);
                hnf = (uu___313_11778.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___313_11778.do_not_unfold_pure_lets);
                unfold_until = (uu___313_11778.unfold_until);
                unfold_only = (uu___313_11778.unfold_only);
                unfold_fully = (uu___313_11778.unfold_fully);
                unfold_attr = (uu___313_11778.unfold_attr);
                unfold_tac = (uu___313_11778.unfold_tac);
                pure_subterms_within_computations =
                  (uu___313_11778.pure_subterms_within_computations);
                simplify = (uu___313_11778.simplify);
                erase_universes = (uu___313_11778.erase_universes);
                allow_unbound_universes =
                  (uu___313_11778.allow_unbound_universes);
                reify_ = (uu___313_11778.reify_);
                compress_uvars = (uu___313_11778.compress_uvars);
                no_full_norm = (uu___313_11778.no_full_norm);
                check_no_uvars = (uu___313_11778.check_no_uvars);
                unmeta = (uu___313_11778.unmeta);
                unascribe = (uu___313_11778.unascribe);
                in_full_norm_request = (uu___313_11778.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___313_11778.weakly_reduce_scrutinee)
              });
           tcenv = (uu___312_11775.tcenv);
           debug = (uu___312_11775.debug);
           delta_level = (uu___312_11775.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___312_11775.strong);
           memoize_lazy = (uu___312_11775.memoize_lazy);
           normalize_pure_lets = (uu___312_11775.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11785 .
    FStar_Syntax_Syntax.term -> 'Auu____11785 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11800 =
        let uu____11807 =
          let uu____11808 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11808.FStar_Syntax_Syntax.n  in
        (uu____11807, args)  in
      match uu____11800 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11814::uu____11815::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11819::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11824::uu____11825::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11828 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___250_11841  ->
    match uu___250_11841 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11847 =
          let uu____11850 =
            let uu____11851 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11851  in
          [uu____11850]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11847
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11857 =
          let uu____11860 =
            let uu____11861 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11861  in
          [uu____11860]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11857
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11884 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11884)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11935 =
            let uu____11940 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11940 s  in
          match uu____11935 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11956 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11956
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11982::(tm,uu____11984)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____12013)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____12034)::uu____12035::(tm,uu____12037)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____12078 =
              let uu____12083 = full_norm steps  in parse_steps uu____12083
               in
            (match uu____12078 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____12122 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___251_12141  ->
    match uu___251_12141 with
    | (App
        (uu____12144,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12145;
                       FStar_Syntax_Syntax.vars = uu____12146;_},uu____12147,uu____12148))::uu____12149
        -> true
    | uu____12154 -> false
  
let firstn :
  'Auu____12163 .
    Prims.int ->
      'Auu____12163 Prims.list ->
        ('Auu____12163 Prims.list,'Auu____12163 Prims.list)
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
          (uu____12205,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12206;
                         FStar_Syntax_Syntax.vars = uu____12207;_},uu____12208,uu____12209))::uu____12210
          -> (cfg.steps).reify_
      | uu____12215 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____12238) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____12248) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____12269  ->
                  match uu____12269 with
                  | (a,uu____12279) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12289 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____12312 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____12313 -> false
    | FStar_Syntax_Syntax.Tm_type uu____12326 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____12327 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____12328 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____12329 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____12330 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____12331 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____12338 -> false
    | FStar_Syntax_Syntax.Tm_let uu____12345 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____12358 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____12377 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____12392 -> true
    | FStar_Syntax_Syntax.Tm_match uu____12399 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____12469  ->
                   match uu____12469 with
                   | (a,uu____12479) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12490) ->
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
                     (fun uu____12618  ->
                        match uu____12618 with
                        | (a,uu____12628) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____12637,uu____12638,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____12644,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____12650 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____12657 -> false
            | FStar_Syntax_Syntax.Meta_named uu____12658 -> false))
  
let decide_unfolding :
  'Auu____12673 .
    cfg ->
      'Auu____12673 Prims.list ->
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
                (fun uu____12765  ->
                   let uu____12766 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____12767 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____12768 =
                     let uu____12769 =
                       let uu____12772 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____12772
                        in
                     stack_to_string uu____12769  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____12766 uu____12767 uu____12768);
              (let attrs =
                 let uu____12798 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____12798 with
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
                   (fun uu____12926  ->
                      fun uu____12927  ->
                        match (uu____12926, uu____12927) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____12987 =
                 match uu____12987 with
                 | (x,y,z) ->
                     let uu____12997 = FStar_Util.string_of_bool x  in
                     let uu____12998 = FStar_Util.string_of_bool y  in
                     let uu____12999 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____12997 uu____12998
                       uu____12999
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____13045 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____13091  ->
                           let uu____13092 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____13093 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____13092 uu____13093);
                      if b then reif else no)
                 | uu____13101 when
                     let uu____13142 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____13142 ->
                     (log_unfolding cfg
                        (fun uu____13147  ->
                           FStar_Util.print_string
                             " >> It's a primop, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____13149),uu____13150);
                        FStar_Syntax_Syntax.sigrng = uu____13151;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____13153;
                        FStar_Syntax_Syntax.sigattrs = uu____13154;_},uu____13155),uu____13156),uu____13157,uu____13158,uu____13159)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (log_unfolding cfg
                        (fun uu____13264  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____13265,uu____13266,uu____13267,uu____13268) when
                     (cfg.steps).unfold_tac &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (log_unfolding cfg
                        (fun uu____13335  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____13337),uu____13338);
                        FStar_Syntax_Syntax.sigrng = uu____13339;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____13341;
                        FStar_Syntax_Syntax.sigattrs = uu____13342;_},uu____13343),uu____13344),uu____13345,uu____13346,uu____13347)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     (log_unfolding cfg
                        (fun uu____13452  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____13453,FStar_Pervasives_Native.Some
                    uu____13454,uu____13455,uu____13456) ->
                     (log_unfolding cfg
                        (fun uu____13524  ->
                           let uu____13525 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13525);
                      (let uu____13526 =
                         let uu____13535 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13555 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13555
                            in
                         let uu____13562 =
                           let uu____13571 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13591 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13591
                              in
                           let uu____13600 =
                             let uu____13609 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13629 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13629
                                in
                             [uu____13609]  in
                           uu____13571 :: uu____13600  in
                         uu____13535 :: uu____13562  in
                       comb_or uu____13526))
                 | (uu____13660,uu____13661,FStar_Pervasives_Native.Some
                    uu____13662,uu____13663) ->
                     (log_unfolding cfg
                        (fun uu____13731  ->
                           let uu____13732 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13732);
                      (let uu____13733 =
                         let uu____13742 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13762 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13762
                            in
                         let uu____13769 =
                           let uu____13778 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13798 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13798
                              in
                           let uu____13807 =
                             let uu____13816 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13836 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13836
                                in
                             [uu____13816]  in
                           uu____13778 :: uu____13807  in
                         uu____13742 :: uu____13769  in
                       comb_or uu____13733))
                 | (uu____13867,uu____13868,uu____13869,FStar_Pervasives_Native.Some
                    uu____13870) ->
                     (log_unfolding cfg
                        (fun uu____13938  ->
                           let uu____13939 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13939);
                      (let uu____13940 =
                         let uu____13949 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13969 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13969
                            in
                         let uu____13976 =
                           let uu____13985 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____14005 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____14005
                              in
                           let uu____14014 =
                             let uu____14023 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____14043 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____14043
                                in
                             [uu____14023]  in
                           uu____13985 :: uu____14014  in
                         uu____13949 :: uu____13976  in
                       comb_or uu____13940))
                 | uu____14074 ->
                     (log_unfolding cfg
                        (fun uu____14120  ->
                           let uu____14121 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____14122 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____14123 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____14121 uu____14122 uu____14123);
                      (let uu____14124 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___252_14128  ->
                                 match uu___252_14128 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____14124))
                  in
               log_unfolding cfg
                 (fun uu____14141  ->
                    let uu____14142 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____14143 = FStar_Range.string_of_range rng  in
                    let uu____14144 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____14142 uu____14143 uu____14144);
               (match res with
                | (false ,uu____14153,uu____14154) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___314_14170 = cfg  in
                      {
                        steps =
                          (let uu___315_14173 = cfg.steps  in
                           {
                             beta = (uu___315_14173.beta);
                             iota = (uu___315_14173.iota);
                             zeta = (uu___315_14173.zeta);
                             weak = (uu___315_14173.weak);
                             hnf = (uu___315_14173.hnf);
                             primops = (uu___315_14173.primops);
                             do_not_unfold_pure_lets =
                               (uu___315_14173.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___315_14173.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___315_14173.pure_subterms_within_computations);
                             simplify = (uu___315_14173.simplify);
                             erase_universes =
                               (uu___315_14173.erase_universes);
                             allow_unbound_universes =
                               (uu___315_14173.allow_unbound_universes);
                             reify_ = (uu___315_14173.reify_);
                             compress_uvars = (uu___315_14173.compress_uvars);
                             no_full_norm = (uu___315_14173.no_full_norm);
                             check_no_uvars = (uu___315_14173.check_no_uvars);
                             unmeta = (uu___315_14173.unmeta);
                             unascribe = (uu___315_14173.unascribe);
                             in_full_norm_request =
                               (uu___315_14173.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___315_14173.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___314_14170.tcenv);
                        debug = (uu___314_14170.debug);
                        delta_level = (uu___314_14170.delta_level);
                        primitive_steps = (uu___314_14170.primitive_steps);
                        strong = (uu___314_14170.strong);
                        memoize_lazy = (uu___314_14170.memoize_lazy);
                        normalize_pure_lets =
                          (uu___314_14170.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____14191 =
                      let uu____14198 = FStar_List.tl stack  in
                      (cfg, uu____14198)  in
                    FStar_Pervasives_Native.Some uu____14191
                | uu____14209 ->
                    let uu____14216 =
                      let uu____14217 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____14217
                       in
                    FStar_All.pipe_left failwith uu____14216))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____14533 ->
                   let uu____14556 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____14556
               | uu____14557 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____14565  ->
               let uu____14566 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____14567 = FStar_Syntax_Print.term_to_string t1  in
               let uu____14568 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____14575 =
                 let uu____14576 =
                   let uu____14579 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____14579
                    in
                 stack_to_string uu____14576  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____14566 uu____14567 uu____14568 uu____14575);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____14605  ->
                     let uu____14606 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14606);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____14607 ->
               (log_unfolding cfg
                  (fun uu____14611  ->
                     let uu____14612 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14612);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____14613 ->
               (log_unfolding cfg
                  (fun uu____14617  ->
                     let uu____14618 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14618);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____14619 ->
               (log_unfolding cfg
                  (fun uu____14623  ->
                     let uu____14624 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14624);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14625;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____14626;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____14632  ->
                     let uu____14633 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14633);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14634;
                 FStar_Syntax_Syntax.fv_delta = uu____14635;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____14639  ->
                     let uu____14640 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14640);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14641;
                 FStar_Syntax_Syntax.fv_delta = uu____14642;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____14643);_}
               ->
               (log_unfolding cfg
                  (fun uu____14653  ->
                     let uu____14654 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14654);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14657 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14657  in
               let uu____14658 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14658 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____14691 ->
               let uu____14698 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14698
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____14734 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____14734)
               ->
               let cfg' =
                 let uu___316_14736 = cfg  in
                 {
                   steps =
                     (let uu___317_14739 = cfg.steps  in
                      {
                        beta = (uu___317_14739.beta);
                        iota = (uu___317_14739.iota);
                        zeta = (uu___317_14739.zeta);
                        weak = (uu___317_14739.weak);
                        hnf = (uu___317_14739.hnf);
                        primops = (uu___317_14739.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___317_14739.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___317_14739.unfold_attr);
                        unfold_tac = (uu___317_14739.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___317_14739.pure_subterms_within_computations);
                        simplify = (uu___317_14739.simplify);
                        erase_universes = (uu___317_14739.erase_universes);
                        allow_unbound_universes =
                          (uu___317_14739.allow_unbound_universes);
                        reify_ = (uu___317_14739.reify_);
                        compress_uvars = (uu___317_14739.compress_uvars);
                        no_full_norm = (uu___317_14739.no_full_norm);
                        check_no_uvars = (uu___317_14739.check_no_uvars);
                        unmeta = (uu___317_14739.unmeta);
                        unascribe = (uu___317_14739.unascribe);
                        in_full_norm_request =
                          (uu___317_14739.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___317_14739.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___316_14736.tcenv);
                   debug = (uu___316_14736.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___316_14736.primitive_steps);
                   strong = (uu___316_14736.strong);
                   memoize_lazy = (uu___316_14736.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____14744 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____14744 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14775  ->
                              fun stack1  ->
                                match uu____14775 with
                                | (a,aq) ->
                                    let uu____14787 =
                                      let uu____14788 =
                                        let uu____14795 =
                                          let uu____14796 =
                                            let uu____14827 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14827, false)  in
                                          Clos uu____14796  in
                                        (uu____14795, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14788  in
                                    uu____14787 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14915  ->
                          let uu____14916 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14916);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14940 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___253_14945  ->
                                match uu___253_14945 with
                                | UnfoldUntil uu____14946 -> true
                                | UnfoldOnly uu____14947 -> true
                                | UnfoldFully uu____14950 -> true
                                | uu____14953 -> false))
                         in
                      if uu____14940
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___318_14958 = cfg  in
                      let uu____14959 =
                        let uu___319_14960 = to_fsteps s  in
                        {
                          beta = (uu___319_14960.beta);
                          iota = (uu___319_14960.iota);
                          zeta = (uu___319_14960.zeta);
                          weak = (uu___319_14960.weak);
                          hnf = (uu___319_14960.hnf);
                          primops = (uu___319_14960.primops);
                          do_not_unfold_pure_lets =
                            (uu___319_14960.do_not_unfold_pure_lets);
                          unfold_until = (uu___319_14960.unfold_until);
                          unfold_only = (uu___319_14960.unfold_only);
                          unfold_fully = (uu___319_14960.unfold_fully);
                          unfold_attr = (uu___319_14960.unfold_attr);
                          unfold_tac = (uu___319_14960.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___319_14960.pure_subterms_within_computations);
                          simplify = (uu___319_14960.simplify);
                          erase_universes = (uu___319_14960.erase_universes);
                          allow_unbound_universes =
                            (uu___319_14960.allow_unbound_universes);
                          reify_ = (uu___319_14960.reify_);
                          compress_uvars = (uu___319_14960.compress_uvars);
                          no_full_norm = (uu___319_14960.no_full_norm);
                          check_no_uvars = (uu___319_14960.check_no_uvars);
                          unmeta = (uu___319_14960.unmeta);
                          unascribe = (uu___319_14960.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___319_14960.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14959;
                        tcenv = (uu___318_14958.tcenv);
                        debug = (uu___318_14958.debug);
                        delta_level;
                        primitive_steps = (uu___318_14958.primitive_steps);
                        strong = (uu___318_14958.strong);
                        memoize_lazy = (uu___318_14958.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14965 =
                          let uu____14966 =
                            let uu____14971 = FStar_Util.now ()  in
                            (t1, uu____14971)  in
                          Debug uu____14966  in
                        uu____14965 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14975 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14975
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14984 =
                      let uu____14991 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14991, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14984  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____15000 = lookup_bvar env x  in
               (match uu____15000 with
                | Univ uu____15001 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____15050 = FStar_ST.op_Bang r  in
                      (match uu____15050 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____15172  ->
                                 let uu____15173 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____15174 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____15173
                                   uu____15174);
                            (let uu____15175 = maybe_weakly_reduced t'  in
                             if uu____15175
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____15176 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____15251)::uu____15252 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____15262,uu____15263))::stack_rest ->
                    (match c with
                     | Univ uu____15267 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____15276 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____15305  ->
                                    let uu____15306 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____15306);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____15340  ->
                                    let uu____15341 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____15341);
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
                       (fun uu____15409  ->
                          let uu____15410 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____15410);
                     norm cfg env stack1 t1)
                | (Match uu____15411)::uu____15412 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___320_15426 = cfg.steps  in
                             {
                               beta = (uu___320_15426.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_15426.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_15426.unfold_until);
                               unfold_only = (uu___320_15426.unfold_only);
                               unfold_fully = (uu___320_15426.unfold_fully);
                               unfold_attr = (uu___320_15426.unfold_attr);
                               unfold_tac = (uu___320_15426.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_15426.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_15426.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_15426.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_15426.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_15426.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_15426.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_15428 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_15428.tcenv);
                               debug = (uu___321_15428.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_15428.primitive_steps);
                               strong = (uu___321_15428.strong);
                               memoize_lazy = (uu___321_15428.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_15428.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15430 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15430 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15466  -> dummy :: env1) env)
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
                                          let uu____15509 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15509)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_15516 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_15516.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_15516.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15517 -> lopt  in
                           (log cfg
                              (fun uu____15523  ->
                                 let uu____15524 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15524);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_15535 = cfg  in
                               {
                                 steps = (uu___323_15535.steps);
                                 tcenv = (uu___323_15535.tcenv);
                                 debug = (uu___323_15535.debug);
                                 delta_level = (uu___323_15535.delta_level);
                                 primitive_steps =
                                   (uu___323_15535.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_15535.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_15535.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____15538)::uu____15539 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___320_15549 = cfg.steps  in
                             {
                               beta = (uu___320_15549.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_15549.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_15549.unfold_until);
                               unfold_only = (uu___320_15549.unfold_only);
                               unfold_fully = (uu___320_15549.unfold_fully);
                               unfold_attr = (uu___320_15549.unfold_attr);
                               unfold_tac = (uu___320_15549.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_15549.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_15549.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_15549.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_15549.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_15549.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_15549.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_15551 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_15551.tcenv);
                               debug = (uu___321_15551.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_15551.primitive_steps);
                               strong = (uu___321_15551.strong);
                               memoize_lazy = (uu___321_15551.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_15551.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15553 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15553 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15589  -> dummy :: env1) env)
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
                                          let uu____15632 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15632)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_15639 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_15639.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_15639.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15640 -> lopt  in
                           (log cfg
                              (fun uu____15646  ->
                                 let uu____15647 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15647);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_15658 = cfg  in
                               {
                                 steps = (uu___323_15658.steps);
                                 tcenv = (uu___323_15658.tcenv);
                                 debug = (uu___323_15658.debug);
                                 delta_level = (uu___323_15658.delta_level);
                                 primitive_steps =
                                   (uu___323_15658.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_15658.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_15658.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____15661)::uu____15662 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___320_15674 = cfg.steps  in
                             {
                               beta = (uu___320_15674.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_15674.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_15674.unfold_until);
                               unfold_only = (uu___320_15674.unfold_only);
                               unfold_fully = (uu___320_15674.unfold_fully);
                               unfold_attr = (uu___320_15674.unfold_attr);
                               unfold_tac = (uu___320_15674.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_15674.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_15674.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_15674.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_15674.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_15674.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_15674.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_15676 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_15676.tcenv);
                               debug = (uu___321_15676.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_15676.primitive_steps);
                               strong = (uu___321_15676.strong);
                               memoize_lazy = (uu___321_15676.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_15676.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15678 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15678 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15714  -> dummy :: env1) env)
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
                                          let uu____15757 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15757)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_15764 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_15764.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_15764.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15765 -> lopt  in
                           (log cfg
                              (fun uu____15771  ->
                                 let uu____15772 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15772);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_15783 = cfg  in
                               {
                                 steps = (uu___323_15783.steps);
                                 tcenv = (uu___323_15783.tcenv);
                                 debug = (uu___323_15783.debug);
                                 delta_level = (uu___323_15783.delta_level);
                                 primitive_steps =
                                   (uu___323_15783.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_15783.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_15783.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____15786)::uu____15787 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___320_15801 = cfg.steps  in
                             {
                               beta = (uu___320_15801.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_15801.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_15801.unfold_until);
                               unfold_only = (uu___320_15801.unfold_only);
                               unfold_fully = (uu___320_15801.unfold_fully);
                               unfold_attr = (uu___320_15801.unfold_attr);
                               unfold_tac = (uu___320_15801.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_15801.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_15801.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_15801.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_15801.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_15801.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_15801.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_15803 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_15803.tcenv);
                               debug = (uu___321_15803.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_15803.primitive_steps);
                               strong = (uu___321_15803.strong);
                               memoize_lazy = (uu___321_15803.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_15803.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15805 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15805 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15841  -> dummy :: env1) env)
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
                                          let uu____15884 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15884)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_15891 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_15891.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_15891.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15892 -> lopt  in
                           (log cfg
                              (fun uu____15898  ->
                                 let uu____15899 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15899);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_15910 = cfg  in
                               {
                                 steps = (uu___323_15910.steps);
                                 tcenv = (uu___323_15910.tcenv);
                                 debug = (uu___323_15910.debug);
                                 delta_level = (uu___323_15910.delta_level);
                                 primitive_steps =
                                   (uu___323_15910.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_15910.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_15910.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15913)::uu____15914 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___320_15928 = cfg.steps  in
                             {
                               beta = (uu___320_15928.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_15928.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_15928.unfold_until);
                               unfold_only = (uu___320_15928.unfold_only);
                               unfold_fully = (uu___320_15928.unfold_fully);
                               unfold_attr = (uu___320_15928.unfold_attr);
                               unfold_tac = (uu___320_15928.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_15928.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_15928.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_15928.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_15928.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_15928.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_15928.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_15930 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_15930.tcenv);
                               debug = (uu___321_15930.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_15930.primitive_steps);
                               strong = (uu___321_15930.strong);
                               memoize_lazy = (uu___321_15930.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_15930.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15932 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15932 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15968  -> dummy :: env1) env)
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
                                          let uu____16011 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16011)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_16018 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_16018.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_16018.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16019 -> lopt  in
                           (log cfg
                              (fun uu____16025  ->
                                 let uu____16026 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16026);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_16037 = cfg  in
                               {
                                 steps = (uu___323_16037.steps);
                                 tcenv = (uu___323_16037.tcenv);
                                 debug = (uu___323_16037.debug);
                                 delta_level = (uu___323_16037.delta_level);
                                 primitive_steps =
                                   (uu___323_16037.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_16037.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_16037.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____16040)::uu____16041 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___320_16059 = cfg.steps  in
                             {
                               beta = (uu___320_16059.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_16059.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_16059.unfold_until);
                               unfold_only = (uu___320_16059.unfold_only);
                               unfold_fully = (uu___320_16059.unfold_fully);
                               unfold_attr = (uu___320_16059.unfold_attr);
                               unfold_tac = (uu___320_16059.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_16059.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_16059.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_16059.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_16059.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_16059.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_16059.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_16061 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_16061.tcenv);
                               debug = (uu___321_16061.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_16061.primitive_steps);
                               strong = (uu___321_16061.strong);
                               memoize_lazy = (uu___321_16061.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_16061.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16063 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16063 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16099  -> dummy :: env1) env)
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
                                          let uu____16142 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16142)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_16149 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_16149.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_16149.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16150 -> lopt  in
                           (log cfg
                              (fun uu____16156  ->
                                 let uu____16157 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16157);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_16168 = cfg  in
                               {
                                 steps = (uu___323_16168.steps);
                                 tcenv = (uu___323_16168.tcenv);
                                 debug = (uu___323_16168.debug);
                                 delta_level = (uu___323_16168.delta_level);
                                 primitive_steps =
                                   (uu___323_16168.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_16168.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_16168.normalize_pure_lets)
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
                             let uu___320_16174 = cfg.steps  in
                             {
                               beta = (uu___320_16174.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___320_16174.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___320_16174.unfold_until);
                               unfold_only = (uu___320_16174.unfold_only);
                               unfold_fully = (uu___320_16174.unfold_fully);
                               unfold_attr = (uu___320_16174.unfold_attr);
                               unfold_tac = (uu___320_16174.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___320_16174.erase_universes);
                               allow_unbound_universes =
                                 (uu___320_16174.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___320_16174.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___320_16174.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___320_16174.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___320_16174.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___321_16176 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___321_16176.tcenv);
                               debug = (uu___321_16176.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___321_16176.primitive_steps);
                               strong = (uu___321_16176.strong);
                               memoize_lazy = (uu___321_16176.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___321_16176.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____16178 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16178 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16214  -> dummy :: env1) env)
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
                                          let uu____16257 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16257)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___322_16264 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___322_16264.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___322_16264.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16265 -> lopt  in
                           (log cfg
                              (fun uu____16271  ->
                                 let uu____16272 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16272);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___323_16283 = cfg  in
                               {
                                 steps = (uu___323_16283.steps);
                                 tcenv = (uu___323_16283.tcenv);
                                 debug = (uu___323_16283.debug);
                                 delta_level = (uu___323_16283.delta_level);
                                 primitive_steps =
                                   (uu___323_16283.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___323_16283.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___323_16283.normalize_pure_lets)
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
                      (fun uu____16326  ->
                         fun stack1  ->
                           match uu____16326 with
                           | (a,aq) ->
                               let uu____16338 =
                                 let uu____16339 =
                                   let uu____16346 =
                                     let uu____16347 =
                                       let uu____16378 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____16378, false)  in
                                     Clos uu____16347  in
                                   (uu____16346, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____16339  in
                               uu____16338 :: stack1) args)
                  in
               (log cfg
                  (fun uu____16466  ->
                     let uu____16467 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____16467);
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
                             ((let uu___324_16515 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___324_16515.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___324_16515.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____16516 ->
                      let uu____16531 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____16531)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____16534 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____16534 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____16565 =
                          let uu____16566 =
                            let uu____16573 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___325_16579 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___325_16579.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___325_16579.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____16573)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____16566  in
                        mk uu____16565 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____16602 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____16602
               else
                 (let uu____16604 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____16604 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____16612 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____16638  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____16612 c1  in
                      let t2 =
                        let uu____16662 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____16662 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____16775)::uu____16776 ->
                    (log cfg
                       (fun uu____16789  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____16790)::uu____16791 ->
                    (log cfg
                       (fun uu____16802  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____16803,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____16804;
                                   FStar_Syntax_Syntax.vars = uu____16805;_},uu____16806,uu____16807))::uu____16808
                    ->
                    (log cfg
                       (fun uu____16815  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____16816)::uu____16817 ->
                    (log cfg
                       (fun uu____16828  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____16829 ->
                    (log cfg
                       (fun uu____16832  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____16836  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____16861 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____16861
                         | FStar_Util.Inr c ->
                             let uu____16875 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16875
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16898 =
                               let uu____16899 =
                                 let uu____16926 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16926, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16899
                                in
                             mk uu____16898 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16961 ->
                           let uu____16962 =
                             let uu____16963 =
                               let uu____16964 =
                                 let uu____16991 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16991, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16964
                                in
                             mk uu____16963 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16962))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___326_17068 = cfg  in
                   {
                     steps =
                       (let uu___327_17071 = cfg.steps  in
                        {
                          beta = (uu___327_17071.beta);
                          iota = (uu___327_17071.iota);
                          zeta = (uu___327_17071.zeta);
                          weak = true;
                          hnf = (uu___327_17071.hnf);
                          primops = (uu___327_17071.primops);
                          do_not_unfold_pure_lets =
                            (uu___327_17071.do_not_unfold_pure_lets);
                          unfold_until = (uu___327_17071.unfold_until);
                          unfold_only = (uu___327_17071.unfold_only);
                          unfold_fully = (uu___327_17071.unfold_fully);
                          unfold_attr = (uu___327_17071.unfold_attr);
                          unfold_tac = (uu___327_17071.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___327_17071.pure_subterms_within_computations);
                          simplify = (uu___327_17071.simplify);
                          erase_universes = (uu___327_17071.erase_universes);
                          allow_unbound_universes =
                            (uu___327_17071.allow_unbound_universes);
                          reify_ = (uu___327_17071.reify_);
                          compress_uvars = (uu___327_17071.compress_uvars);
                          no_full_norm = (uu___327_17071.no_full_norm);
                          check_no_uvars = (uu___327_17071.check_no_uvars);
                          unmeta = (uu___327_17071.unmeta);
                          unascribe = (uu___327_17071.unascribe);
                          in_full_norm_request =
                            (uu___327_17071.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___327_17071.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___326_17068.tcenv);
                     debug = (uu___326_17068.debug);
                     delta_level = (uu___326_17068.delta_level);
                     primitive_steps = (uu___326_17068.primitive_steps);
                     strong = (uu___326_17068.strong);
                     memoize_lazy = (uu___326_17068.memoize_lazy);
                     normalize_pure_lets =
                       (uu___326_17068.normalize_pure_lets)
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
                         let uu____17107 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____17107 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___328_17127 = cfg  in
                               let uu____17128 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___328_17127.steps);
                                 tcenv = uu____17128;
                                 debug = (uu___328_17127.debug);
                                 delta_level = (uu___328_17127.delta_level);
                                 primitive_steps =
                                   (uu___328_17127.primitive_steps);
                                 strong = (uu___328_17127.strong);
                                 memoize_lazy = (uu___328_17127.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___328_17127.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____17135 =
                                 let uu____17136 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____17136  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____17135
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___329_17139 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___329_17139.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___329_17139.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___329_17139.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___329_17139.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____17140 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____17140
           | FStar_Syntax_Syntax.Tm_let
               ((uu____17151,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____17152;
                               FStar_Syntax_Syntax.lbunivs = uu____17153;
                               FStar_Syntax_Syntax.lbtyp = uu____17154;
                               FStar_Syntax_Syntax.lbeff = uu____17155;
                               FStar_Syntax_Syntax.lbdef = uu____17156;
                               FStar_Syntax_Syntax.lbattrs = uu____17157;
                               FStar_Syntax_Syntax.lbpos = uu____17158;_}::uu____17159),uu____17160)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____17200 =
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
               if uu____17200
               then
                 let binder =
                   let uu____17202 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____17202  in
                 let env1 =
                   let uu____17212 =
                     let uu____17219 =
                       let uu____17220 =
                         let uu____17251 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____17251,
                           false)
                          in
                       Clos uu____17220  in
                     ((FStar_Pervasives_Native.Some binder), uu____17219)  in
                   uu____17212 :: env  in
                 (log cfg
                    (fun uu____17346  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____17350  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____17351 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____17351))
                 else
                   (let uu____17353 =
                      let uu____17358 =
                        let uu____17359 =
                          let uu____17366 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____17366
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____17359]  in
                      FStar_Syntax_Subst.open_term uu____17358 body  in
                    match uu____17353 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____17393  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____17401 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____17401  in
                            FStar_Util.Inl
                              (let uu___330_17417 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___330_17417.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___330_17417.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____17420  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___331_17422 = lb  in
                             let uu____17423 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___331_17422.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___331_17422.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17423;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___331_17422.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___331_17422.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____17452  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___332_17477 = cfg  in
                             {
                               steps = (uu___332_17477.steps);
                               tcenv = (uu___332_17477.tcenv);
                               debug = (uu___332_17477.debug);
                               delta_level = (uu___332_17477.delta_level);
                               primitive_steps =
                                 (uu___332_17477.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___332_17477.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___332_17477.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____17480  ->
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
               let uu____17497 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____17497 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____17533 =
                               let uu___333_17534 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___333_17534.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___333_17534.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____17533  in
                           let uu____17535 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____17535 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____17561 =
                                   FStar_List.map (fun uu____17577  -> dummy)
                                     lbs1
                                    in
                                 let uu____17578 =
                                   let uu____17587 =
                                     FStar_List.map
                                       (fun uu____17609  -> dummy) xs1
                                      in
                                   FStar_List.append uu____17587 env  in
                                 FStar_List.append uu____17561 uu____17578
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____17635 =
                                       let uu___334_17636 = rc  in
                                       let uu____17637 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___334_17636.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____17637;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___334_17636.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____17635
                                 | uu____17646 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___335_17652 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___335_17652.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___335_17652.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___335_17652.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___335_17652.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____17662 =
                        FStar_List.map (fun uu____17678  -> dummy) lbs2  in
                      FStar_List.append uu____17662 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____17686 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____17686 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___336_17702 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___336_17702.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___336_17702.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____17731 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____17731
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____17750 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____17826  ->
                        match uu____17826 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___337_17947 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___337_17947.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___337_17947.FStar_Syntax_Syntax.sort)
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
               (match uu____17750 with
                | (rec_env,memos,uu____18174) ->
                    let uu____18227 =
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
                             let uu____18550 =
                               let uu____18557 =
                                 let uu____18558 =
                                   let uu____18589 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____18589, false)
                                    in
                                 Clos uu____18558  in
                               (FStar_Pervasives_Native.None, uu____18557)
                                in
                             uu____18550 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____18693  ->
                     let uu____18694 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____18694);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____18716 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____18718::uu____18719 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____18724) ->
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
                             | uu____18751 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____18767 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____18767
                              | uu____18780 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____18786 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____18810 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____18824 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____18837 =
                        let uu____18838 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____18839 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____18838 uu____18839
                         in
                      failwith uu____18837
                    else
                      (let uu____18841 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____18841)
                | uu____18842 -> norm cfg env stack t2))

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
              let uu____18851 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____18851 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____18865  ->
                        let uu____18866 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____18866);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____18877  ->
                        let uu____18878 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____18879 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____18878 uu____18879);
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
                      | (UnivArgs (us',uu____18892))::stack1 ->
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
                      | uu____18931 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____18934 ->
                          let uu____18937 =
                            let uu____18938 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____18938
                             in
                          failwith uu____18937
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
                  let uu___338_18962 = cfg  in
                  let uu____18963 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18963;
                    tcenv = (uu___338_18962.tcenv);
                    debug = (uu___338_18962.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___338_18962.primitive_steps);
                    strong = (uu___338_18962.strong);
                    memoize_lazy = (uu___338_18962.memoize_lazy);
                    normalize_pure_lets =
                      (uu___338_18962.normalize_pure_lets)
                  }
                else
                  (let uu___339_18965 = cfg  in
                   {
                     steps =
                       (let uu___340_18968 = cfg.steps  in
                        {
                          beta = (uu___340_18968.beta);
                          iota = (uu___340_18968.iota);
                          zeta = false;
                          weak = (uu___340_18968.weak);
                          hnf = (uu___340_18968.hnf);
                          primops = (uu___340_18968.primops);
                          do_not_unfold_pure_lets =
                            (uu___340_18968.do_not_unfold_pure_lets);
                          unfold_until = (uu___340_18968.unfold_until);
                          unfold_only = (uu___340_18968.unfold_only);
                          unfold_fully = (uu___340_18968.unfold_fully);
                          unfold_attr = (uu___340_18968.unfold_attr);
                          unfold_tac = (uu___340_18968.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___340_18968.pure_subterms_within_computations);
                          simplify = (uu___340_18968.simplify);
                          erase_universes = (uu___340_18968.erase_universes);
                          allow_unbound_universes =
                            (uu___340_18968.allow_unbound_universes);
                          reify_ = (uu___340_18968.reify_);
                          compress_uvars = (uu___340_18968.compress_uvars);
                          no_full_norm = (uu___340_18968.no_full_norm);
                          check_no_uvars = (uu___340_18968.check_no_uvars);
                          unmeta = (uu___340_18968.unmeta);
                          unascribe = (uu___340_18968.unascribe);
                          in_full_norm_request =
                            (uu___340_18968.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___340_18968.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___339_18965.tcenv);
                     debug = (uu___339_18965.debug);
                     delta_level = (uu___339_18965.delta_level);
                     primitive_steps = (uu___339_18965.primitive_steps);
                     strong = (uu___339_18965.strong);
                     memoize_lazy = (uu___339_18965.memoize_lazy);
                     normalize_pure_lets =
                       (uu___339_18965.normalize_pure_lets)
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
                  (fun uu____19002  ->
                     let uu____19003 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____19004 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____19003
                       uu____19004);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____19006 =
                   let uu____19007 = FStar_Syntax_Subst.compress head3  in
                   uu____19007.FStar_Syntax_Syntax.n  in
                 match uu____19006 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____19025 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____19025
                        in
                     let uu____19026 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____19026 with
                      | (uu____19027,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____19037 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____19047 =
                                   let uu____19048 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____19048.FStar_Syntax_Syntax.n  in
                                 match uu____19047 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____19054,uu____19055))
                                     ->
                                     let uu____19064 =
                                       let uu____19065 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____19065.FStar_Syntax_Syntax.n  in
                                     (match uu____19064 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____19071,msrc,uu____19073))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____19082 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____19082
                                      | uu____19083 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____19084 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____19085 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____19085 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___341_19090 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___341_19090.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___341_19090.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___341_19090.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___341_19090.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___341_19090.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____19091 = FStar_List.tl stack  in
                                    let uu____19092 =
                                      let uu____19093 =
                                        let uu____19100 =
                                          let uu____19101 =
                                            let uu____19114 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____19114)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____19101
                                           in
                                        FStar_Syntax_Syntax.mk uu____19100
                                         in
                                      uu____19093
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____19091 uu____19092
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19130 =
                                      let uu____19131 = is_return body  in
                                      match uu____19131 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____19135;
                                            FStar_Syntax_Syntax.vars =
                                              uu____19136;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____19139 -> false  in
                                    if uu____19130
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
                                         let uu____19160 =
                                           let uu____19167 =
                                             let uu____19168 =
                                               let uu____19187 =
                                                 let uu____19196 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____19196]  in
                                               (uu____19187, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____19168
                                              in
                                           FStar_Syntax_Syntax.mk uu____19167
                                            in
                                         uu____19160
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____19238 =
                                           let uu____19239 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____19239.FStar_Syntax_Syntax.n
                                            in
                                         match uu____19238 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____19245::uu____19246::[])
                                             ->
                                             let uu____19251 =
                                               let uu____19258 =
                                                 let uu____19259 =
                                                   let uu____19266 =
                                                     let uu____19267 =
                                                       let uu____19268 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____19268
                                                        in
                                                     let uu____19269 =
                                                       let uu____19272 =
                                                         let uu____19273 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____19273
                                                          in
                                                       [uu____19272]  in
                                                     uu____19267 ::
                                                       uu____19269
                                                      in
                                                   (bind1, uu____19266)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____19259
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____19258
                                                in
                                             uu____19251
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____19279 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____19293 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____19293
                                         then
                                           let uu____19304 =
                                             let uu____19313 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____19313
                                              in
                                           let uu____19314 =
                                             let uu____19325 =
                                               let uu____19334 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____19334
                                                in
                                             [uu____19325]  in
                                           uu____19304 :: uu____19314
                                         else []  in
                                       let reified =
                                         let uu____19371 =
                                           let uu____19378 =
                                             let uu____19379 =
                                               let uu____19396 =
                                                 let uu____19407 =
                                                   let uu____19418 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____19427 =
                                                     let uu____19438 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____19438]  in
                                                   uu____19418 :: uu____19427
                                                    in
                                                 let uu____19471 =
                                                   let uu____19482 =
                                                     let uu____19493 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____19502 =
                                                       let uu____19513 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____19522 =
                                                         let uu____19533 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____19542 =
                                                           let uu____19553 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____19553]  in
                                                         uu____19533 ::
                                                           uu____19542
                                                          in
                                                       uu____19513 ::
                                                         uu____19522
                                                        in
                                                     uu____19493 ::
                                                       uu____19502
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____19482
                                                    in
                                                 FStar_List.append
                                                   uu____19407 uu____19471
                                                  in
                                               (bind_inst, uu____19396)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____19379
                                              in
                                           FStar_Syntax_Syntax.mk uu____19378
                                            in
                                         uu____19371
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____19637  ->
                                            let uu____19638 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____19639 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____19638 uu____19639);
                                       (let uu____19640 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____19640 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____19668 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____19668
                        in
                     let uu____19669 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____19669 with
                      | (uu____19670,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____19707 =
                                  let uu____19708 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____19708.FStar_Syntax_Syntax.n  in
                                match uu____19707 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____19712) -> t2
                                | uu____19717 -> head4  in
                              let uu____19718 =
                                let uu____19719 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____19719.FStar_Syntax_Syntax.n  in
                              match uu____19718 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____19725 -> FStar_Pervasives_Native.None
                               in
                            let uu____19726 = maybe_extract_fv head4  in
                            match uu____19726 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____19736 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____19736
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____19741 = maybe_extract_fv head5
                                     in
                                  match uu____19741 with
                                  | FStar_Pervasives_Native.Some uu____19746
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____19747 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____19752 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____19769 =
                              match uu____19769 with
                              | (e,q) ->
                                  let uu____19782 =
                                    let uu____19783 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____19783.FStar_Syntax_Syntax.n  in
                                  (match uu____19782 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____19798 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____19798
                                   | uu____19799 -> false)
                               in
                            let uu____19800 =
                              let uu____19801 =
                                let uu____19812 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____19812 :: args  in
                              FStar_Util.for_some is_arg_impure uu____19801
                               in
                            if uu____19800
                            then
                              let uu____19837 =
                                let uu____19838 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____19838
                                 in
                              failwith uu____19837
                            else ());
                           (let uu____19840 = maybe_unfold_action head_app
                               in
                            match uu____19840 with
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
                                   (fun uu____19885  ->
                                      let uu____19886 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____19887 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____19886 uu____19887);
                                 (let uu____19888 = FStar_List.tl stack  in
                                  norm cfg env uu____19888 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____19890) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____19914 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____19914  in
                     (log cfg
                        (fun uu____19918  ->
                           let uu____19919 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____19919);
                      (let uu____19920 = FStar_List.tl stack  in
                       norm cfg env uu____19920 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____20041  ->
                               match uu____20041 with
                               | (pat,wopt,tm) ->
                                   let uu____20089 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____20089)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____20121 = FStar_List.tl stack  in
                     norm cfg env uu____20121 tm
                 | uu____20122 -> fallback ())

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
              (fun uu____20136  ->
                 let uu____20137 = FStar_Ident.string_of_lid msrc  in
                 let uu____20138 = FStar_Ident.string_of_lid mtgt  in
                 let uu____20139 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____20137
                   uu____20138 uu____20139);
            (let uu____20140 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____20140
             then
               let ed =
                 let uu____20142 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____20142  in
               let uu____20143 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____20143 with
               | (uu____20144,return_repr) ->
                   let return_inst =
                     let uu____20157 =
                       let uu____20158 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____20158.FStar_Syntax_Syntax.n  in
                     match uu____20157 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____20164::[]) ->
                         let uu____20169 =
                           let uu____20176 =
                             let uu____20177 =
                               let uu____20184 =
                                 let uu____20185 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____20185]  in
                               (return_tm, uu____20184)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____20177  in
                           FStar_Syntax_Syntax.mk uu____20176  in
                         uu____20169 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____20191 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____20194 =
                     let uu____20201 =
                       let uu____20202 =
                         let uu____20219 =
                           let uu____20230 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____20239 =
                             let uu____20250 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____20250]  in
                           uu____20230 :: uu____20239  in
                         (return_inst, uu____20219)  in
                       FStar_Syntax_Syntax.Tm_app uu____20202  in
                     FStar_Syntax_Syntax.mk uu____20201  in
                   uu____20194 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____20299 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____20299 with
                | FStar_Pervasives_Native.None  ->
                    let uu____20302 =
                      let uu____20303 = FStar_Ident.text_of_lid msrc  in
                      let uu____20304 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____20303 uu____20304
                       in
                    failwith uu____20302
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____20305;
                      FStar_TypeChecker_Env.mtarget = uu____20306;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____20307;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____20329 =
                      let uu____20330 = FStar_Ident.text_of_lid msrc  in
                      let uu____20331 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____20330 uu____20331
                       in
                    failwith uu____20329
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____20332;
                      FStar_TypeChecker_Env.mtarget = uu____20333;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____20334;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____20369 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____20370 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____20369 t FStar_Syntax_Syntax.tun uu____20370))

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
                (fun uu____20440  ->
                   match uu____20440 with
                   | (a,imp) ->
                       let uu____20459 = norm cfg env [] a  in
                       (uu____20459, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____20469  ->
             let uu____20470 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____20471 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____20470 uu____20471);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20495 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____20495
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___342_20498 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___342_20498.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___342_20498.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20520 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____20520
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___343_20523 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___343_20523.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___343_20523.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____20568  ->
                      match uu____20568 with
                      | (a,i) ->
                          let uu____20587 = norm cfg env [] a  in
                          (uu____20587, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___254_20609  ->
                       match uu___254_20609 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____20613 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____20613
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___344_20621 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___345_20624 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___345_20624.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___344_20621.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___344_20621.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____20627  ->
        match uu____20627 with
        | (x,imp) ->
            let uu____20634 =
              let uu___346_20635 = x  in
              let uu____20636 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___346_20635.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___346_20635.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____20636
              }  in
            (uu____20634, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____20644 =
          FStar_List.fold_left
            (fun uu____20678  ->
               fun b  ->
                 match uu____20678 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____20644 with | (nbs,uu____20758) -> FStar_List.rev nbs

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
            let uu____20790 =
              let uu___347_20791 = rc  in
              let uu____20792 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___347_20791.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____20792;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___347_20791.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____20790
        | uu____20801 -> lopt

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
            (let uu____20824 = FStar_Syntax_Print.term_to_string tm  in
             let uu____20825 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____20824
               uu____20825)
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
          let uu____20851 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____20851
          then tm1
          else
            (let w t =
               let uu___348_20865 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___348_20865.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___348_20865.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____20876 =
                 let uu____20877 = FStar_Syntax_Util.unmeta t  in
                 uu____20877.FStar_Syntax_Syntax.n  in
               match uu____20876 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____20884 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____20945)::args1,(bv,uu____20948)::bs1) ->
                   let uu____21002 =
                     let uu____21003 = FStar_Syntax_Subst.compress t  in
                     uu____21003.FStar_Syntax_Syntax.n  in
                   (match uu____21002 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____21007 -> false)
               | ([],[]) -> true
               | (uu____21036,uu____21037) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____21086 = FStar_Syntax_Print.term_to_string t  in
                  let uu____21087 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____21086
                    uu____21087)
               else ();
               (let uu____21089 = FStar_Syntax_Util.head_and_args' t  in
                match uu____21089 with
                | (hd1,args) ->
                    let uu____21128 =
                      let uu____21129 = FStar_Syntax_Subst.compress hd1  in
                      uu____21129.FStar_Syntax_Syntax.n  in
                    (match uu____21128 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____21136 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____21137 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____21138 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____21136 uu____21137 uu____21138)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____21140 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____21157 = FStar_Syntax_Print.term_to_string t  in
                  let uu____21158 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____21157
                    uu____21158)
               else ();
               (let uu____21160 = FStar_Syntax_Util.is_squash t  in
                match uu____21160 with
                | FStar_Pervasives_Native.Some (uu____21171,t') ->
                    is_applied bs t'
                | uu____21183 ->
                    let uu____21192 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____21192 with
                     | FStar_Pervasives_Native.Some (uu____21203,t') ->
                         is_applied bs t'
                     | uu____21215 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____21239 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____21239 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____21246)::(q,uu____21248)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____21290 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____21291 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____21290 uu____21291)
                    else ();
                    (let uu____21293 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____21293 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21298 =
                           let uu____21299 = FStar_Syntax_Subst.compress p
                              in
                           uu____21299.FStar_Syntax_Syntax.n  in
                         (match uu____21298 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____21307 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____21307))
                          | uu____21310 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____21313)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____21338 =
                           let uu____21339 = FStar_Syntax_Subst.compress p1
                              in
                           uu____21339.FStar_Syntax_Syntax.n  in
                         (match uu____21338 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____21347 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____21347))
                          | uu____21350 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____21354 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____21354 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____21359 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____21359 with
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
                                     let uu____21370 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21370))
                               | uu____21373 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____21378)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____21403 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____21403 with
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
                                     let uu____21414 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21414))
                               | uu____21417 -> FStar_Pervasives_Native.None)
                          | uu____21420 -> FStar_Pervasives_Native.None)
                     | uu____21423 -> FStar_Pervasives_Native.None))
               | uu____21426 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____21439 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____21439 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____21445)::[],uu____21446,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____21465 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____21466 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____21465
                         uu____21466)
                    else ();
                    is_quantified_const bv phi')
               | uu____21468 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____21481 =
                 let uu____21482 = FStar_Syntax_Subst.compress phi  in
                 uu____21482.FStar_Syntax_Syntax.n  in
               match uu____21481 with
               | FStar_Syntax_Syntax.Tm_match (uu____21487,br::brs) ->
                   let uu____21554 = br  in
                   (match uu____21554 with
                    | (uu____21571,uu____21572,e) ->
                        let r =
                          let uu____21593 = simp_t e  in
                          match uu____21593 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____21599 =
                                FStar_List.for_all
                                  (fun uu____21617  ->
                                     match uu____21617 with
                                     | (uu____21630,uu____21631,e') ->
                                         let uu____21645 = simp_t e'  in
                                         uu____21645 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____21599
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____21653 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____21662 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____21662
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____21697 =
                 match uu____21697 with
                 | (t1,q) ->
                     let uu____21718 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____21718 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____21750 -> (t1, q))
                  in
               let uu____21763 = FStar_Syntax_Util.head_and_args t  in
               match uu____21763 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____21841 =
                 let uu____21842 = FStar_Syntax_Util.unmeta ty  in
                 uu____21842.FStar_Syntax_Syntax.n  in
               match uu____21841 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____21846) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____21851,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____21875 -> false  in
             let simplify1 arg =
               let uu____21906 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____21906, arg)  in
             let uu____21919 = is_forall_const tm1  in
             match uu____21919 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____21924 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____21925 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____21924
                       uu____21925)
                  else ();
                  (let uu____21927 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____21927))
             | FStar_Pervasives_Native.None  ->
                 let uu____21928 =
                   let uu____21929 = FStar_Syntax_Subst.compress tm1  in
                   uu____21929.FStar_Syntax_Syntax.n  in
                 (match uu____21928 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____21933;
                              FStar_Syntax_Syntax.vars = uu____21934;_},uu____21935);
                         FStar_Syntax_Syntax.pos = uu____21936;
                         FStar_Syntax_Syntax.vars = uu____21937;_},args)
                      ->
                      let uu____21967 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21967
                      then
                        let uu____21968 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21968 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22023)::
                             (uu____22024,(arg,uu____22026))::[] ->
                             maybe_auto_squash arg
                         | (uu____22091,(arg,uu____22093))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22094)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22159)::uu____22160::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22223::(FStar_Pervasives_Native.Some (false
                                         ),uu____22224)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22287 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22303 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22303
                         then
                           let uu____22304 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22304 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22359)::uu____22360::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22423::(FStar_Pervasives_Native.Some (true
                                           ),uu____22424)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22487)::(uu____22488,(arg,uu____22490))::[]
                               -> maybe_auto_squash arg
                           | (uu____22555,(arg,uu____22557))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22558)::[]
                               -> maybe_auto_squash arg
                           | uu____22623 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22639 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22639
                            then
                              let uu____22640 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22640 with
                              | uu____22695::(FStar_Pervasives_Native.Some
                                              (true ),uu____22696)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22759)::uu____22760::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22823)::(uu____22824,(arg,uu____22826))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22891,(p,uu____22893))::(uu____22894,
                                                                (q,uu____22896))::[]
                                  ->
                                  let uu____22961 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22961
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22963 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22979 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22979
                               then
                                 let uu____22980 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22980 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23035)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23036)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23101)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23102)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23167)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23168)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23233)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23234)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23299,(arg,uu____23301))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23302)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23367)::(uu____23368,(arg,uu____23370))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23435,(arg,uu____23437))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23438)::[]
                                     ->
                                     let uu____23503 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23503
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23504)::(uu____23505,(arg,uu____23507))::[]
                                     ->
                                     let uu____23572 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23572
                                 | (uu____23573,(p,uu____23575))::(uu____23576,
                                                                   (q,uu____23578))::[]
                                     ->
                                     let uu____23643 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23643
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23645 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23661 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23661
                                  then
                                    let uu____23662 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23662 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23717)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23756)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23795 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23811 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23811
                                     then
                                       match args with
                                       | (t,uu____23813)::[] ->
                                           let uu____23838 =
                                             let uu____23839 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23839.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23838 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23842::[],body,uu____23844)
                                                ->
                                                let uu____23879 = simp_t body
                                                   in
                                                (match uu____23879 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23882 -> tm1)
                                            | uu____23885 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23887))::(t,uu____23889)::[]
                                           ->
                                           let uu____23928 =
                                             let uu____23929 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23929.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23928 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23932::[],body,uu____23934)
                                                ->
                                                let uu____23969 = simp_t body
                                                   in
                                                (match uu____23969 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23972 -> tm1)
                                            | uu____23975 -> tm1)
                                       | uu____23976 -> tm1
                                     else
                                       (let uu____23988 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23988
                                        then
                                          match args with
                                          | (t,uu____23990)::[] ->
                                              let uu____24015 =
                                                let uu____24016 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24016.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24015 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24019::[],body,uu____24021)
                                                   ->
                                                   let uu____24056 =
                                                     simp_t body  in
                                                   (match uu____24056 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24059 -> tm1)
                                               | uu____24062 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24064))::(t,uu____24066)::[]
                                              ->
                                              let uu____24105 =
                                                let uu____24106 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24106.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24105 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24109::[],body,uu____24111)
                                                   ->
                                                   let uu____24146 =
                                                     simp_t body  in
                                                   (match uu____24146 with
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
                                                    | uu____24149 -> tm1)
                                               | uu____24152 -> tm1)
                                          | uu____24153 -> tm1
                                        else
                                          (let uu____24165 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24165
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24166;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24167;_},uu____24168)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24193;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24194;_},uu____24195)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24220 -> tm1
                                           else
                                             (let uu____24232 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24232 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24252 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____24264;
                         FStar_Syntax_Syntax.vars = uu____24265;_},args)
                      ->
                      let uu____24291 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____24291
                      then
                        let uu____24292 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____24292 with
                         | (FStar_Pervasives_Native.Some (true ),uu____24347)::
                             (uu____24348,(arg,uu____24350))::[] ->
                             maybe_auto_squash arg
                         | (uu____24415,(arg,uu____24417))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____24418)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____24483)::uu____24484::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____24547::(FStar_Pervasives_Native.Some (false
                                         ),uu____24548)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____24611 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____24627 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____24627
                         then
                           let uu____24628 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____24628 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____24683)::uu____24684::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____24747::(FStar_Pervasives_Native.Some (true
                                           ),uu____24748)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____24811)::(uu____24812,(arg,uu____24814))::[]
                               -> maybe_auto_squash arg
                           | (uu____24879,(arg,uu____24881))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____24882)::[]
                               -> maybe_auto_squash arg
                           | uu____24947 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____24963 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____24963
                            then
                              let uu____24964 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____24964 with
                              | uu____25019::(FStar_Pervasives_Native.Some
                                              (true ),uu____25020)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____25083)::uu____25084::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____25147)::(uu____25148,(arg,uu____25150))::[]
                                  -> maybe_auto_squash arg
                              | (uu____25215,(p,uu____25217))::(uu____25218,
                                                                (q,uu____25220))::[]
                                  ->
                                  let uu____25285 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____25285
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____25287 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____25303 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____25303
                               then
                                 let uu____25304 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____25304 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25359)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25360)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25425)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25426)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25491)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25492)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25557)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25558)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____25623,(arg,uu____25625))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____25626)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25691)::(uu____25692,(arg,uu____25694))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____25759,(arg,uu____25761))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____25762)::[]
                                     ->
                                     let uu____25827 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25827
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25828)::(uu____25829,(arg,uu____25831))::[]
                                     ->
                                     let uu____25896 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25896
                                 | (uu____25897,(p,uu____25899))::(uu____25900,
                                                                   (q,uu____25902))::[]
                                     ->
                                     let uu____25967 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____25967
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____25969 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____25985 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____25985
                                  then
                                    let uu____25986 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____25986 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____26041)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____26080)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____26119 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____26135 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____26135
                                     then
                                       match args with
                                       | (t,uu____26137)::[] ->
                                           let uu____26162 =
                                             let uu____26163 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____26163.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____26162 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____26166::[],body,uu____26168)
                                                ->
                                                let uu____26203 = simp_t body
                                                   in
                                                (match uu____26203 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____26206 -> tm1)
                                            | uu____26209 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____26211))::(t,uu____26213)::[]
                                           ->
                                           let uu____26252 =
                                             let uu____26253 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____26253.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____26252 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____26256::[],body,uu____26258)
                                                ->
                                                let uu____26293 = simp_t body
                                                   in
                                                (match uu____26293 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____26296 -> tm1)
                                            | uu____26299 -> tm1)
                                       | uu____26300 -> tm1
                                     else
                                       (let uu____26312 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____26312
                                        then
                                          match args with
                                          | (t,uu____26314)::[] ->
                                              let uu____26339 =
                                                let uu____26340 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26340.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26339 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26343::[],body,uu____26345)
                                                   ->
                                                   let uu____26380 =
                                                     simp_t body  in
                                                   (match uu____26380 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____26383 -> tm1)
                                               | uu____26386 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____26388))::(t,uu____26390)::[]
                                              ->
                                              let uu____26429 =
                                                let uu____26430 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26430.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26429 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26433::[],body,uu____26435)
                                                   ->
                                                   let uu____26470 =
                                                     simp_t body  in
                                                   (match uu____26470 with
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
                                                    | uu____26473 -> tm1)
                                               | uu____26476 -> tm1)
                                          | uu____26477 -> tm1
                                        else
                                          (let uu____26489 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____26489
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26490;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26491;_},uu____26492)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26517;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26518;_},uu____26519)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____26544 -> tm1
                                           else
                                             (let uu____26556 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____26556 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____26576 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____26593 = simp_t t  in
                      (match uu____26593 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____26596 ->
                      let uu____26619 = is_const_match tm1  in
                      (match uu____26619 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____26622 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____26632  ->
               (let uu____26634 = FStar_Syntax_Print.tag_of_term t  in
                let uu____26635 = FStar_Syntax_Print.term_to_string t  in
                let uu____26636 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____26643 =
                  let uu____26644 =
                    let uu____26647 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____26647
                     in
                  stack_to_string uu____26644  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____26634 uu____26635 uu____26636 uu____26643);
               (let uu____26670 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____26670
                then
                  let uu____26671 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____26671 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____26678 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____26679 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____26680 =
                          let uu____26681 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____26681
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____26678
                          uu____26679 uu____26680);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____26699 =
                     let uu____26700 =
                       let uu____26701 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____26701  in
                     FStar_Util.string_of_int uu____26700  in
                   let uu____26706 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____26707 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____26699 uu____26706 uu____26707)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____26713,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____26764  ->
                     let uu____26765 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____26765);
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
               let uu____26803 =
                 let uu___349_26804 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___349_26804.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___349_26804.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____26803
           | (Arg (Univ uu____26807,uu____26808,uu____26809))::uu____26810 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____26813,uu____26814))::uu____26815 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____26830,uu____26831),aq,r))::stack1
               when
               let uu____26881 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____26881 ->
               let t2 =
                 let uu____26885 =
                   let uu____26890 =
                     let uu____26891 = closure_as_term cfg env_arg tm  in
                     (uu____26891, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____26890  in
                 uu____26885 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____26903),aq,r))::stack1 ->
               (log cfg
                  (fun uu____26956  ->
                     let uu____26957 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____26957);
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
                  (let uu____26971 = FStar_ST.op_Bang m  in
                   match uu____26971 with
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
                   | FStar_Pervasives_Native.Some (uu____27116,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____27171 =
                 log cfg
                   (fun uu____27175  ->
                      let uu____27176 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____27176);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____27184 =
                 let uu____27185 = FStar_Syntax_Subst.compress t1  in
                 uu____27185.FStar_Syntax_Syntax.n  in
               (match uu____27184 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____27212 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____27212  in
                    (log cfg
                       (fun uu____27216  ->
                          let uu____27217 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____27217);
                     (let uu____27218 = FStar_List.tl stack  in
                      norm cfg env1 uu____27218 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____27219);
                       FStar_Syntax_Syntax.pos = uu____27220;
                       FStar_Syntax_Syntax.vars = uu____27221;_},(e,uu____27223)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____27262 when
                    (cfg.steps).primops ->
                    let uu____27279 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____27279 with
                     | (hd1,args) ->
                         let uu____27322 =
                           let uu____27323 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____27323.FStar_Syntax_Syntax.n  in
                         (match uu____27322 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____27327 = find_prim_step cfg fv  in
                              (match uu____27327 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____27330; arity = uu____27331;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____27333;
                                     requires_binder_substitution =
                                       uu____27334;
                                     interpretation = uu____27335;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____27352 -> fallback " (3)" ())
                          | uu____27355 -> fallback " (4)" ()))
                | uu____27356 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____27381  ->
                     let uu____27382 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____27382);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____27391 =
                   log cfg1
                     (fun uu____27396  ->
                        let uu____27397 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____27398 =
                          let uu____27399 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____27426  ->
                                    match uu____27426 with
                                    | (p,uu____27436,uu____27437) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____27399
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____27397 uu____27398);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___255_27454  ->
                                match uu___255_27454 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____27455 -> false))
                         in
                      let steps =
                        let uu___350_27457 = cfg1.steps  in
                        {
                          beta = (uu___350_27457.beta);
                          iota = (uu___350_27457.iota);
                          zeta = false;
                          weak = (uu___350_27457.weak);
                          hnf = (uu___350_27457.hnf);
                          primops = (uu___350_27457.primops);
                          do_not_unfold_pure_lets =
                            (uu___350_27457.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___350_27457.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___350_27457.pure_subterms_within_computations);
                          simplify = (uu___350_27457.simplify);
                          erase_universes = (uu___350_27457.erase_universes);
                          allow_unbound_universes =
                            (uu___350_27457.allow_unbound_universes);
                          reify_ = (uu___350_27457.reify_);
                          compress_uvars = (uu___350_27457.compress_uvars);
                          no_full_norm = (uu___350_27457.no_full_norm);
                          check_no_uvars = (uu___350_27457.check_no_uvars);
                          unmeta = (uu___350_27457.unmeta);
                          unascribe = (uu___350_27457.unascribe);
                          in_full_norm_request =
                            (uu___350_27457.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___350_27457.weakly_reduce_scrutinee)
                        }  in
                      let uu___351_27462 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___351_27462.tcenv);
                        debug = (uu___351_27462.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___351_27462.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___351_27462.memoize_lazy);
                        normalize_pure_lets =
                          (uu___351_27462.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____27534 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____27563 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____27647  ->
                                    fun uu____27648  ->
                                      match (uu____27647, uu____27648) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____27787 = norm_pat env3 p1
                                             in
                                          (match uu____27787 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____27563 with
                           | (pats1,env3) ->
                               ((let uu___352_27949 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___352_27949.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___353_27968 = x  in
                            let uu____27969 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___353_27968.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___353_27968.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27969
                            }  in
                          ((let uu___354_27983 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___354_27983.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___355_27994 = x  in
                            let uu____27995 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___355_27994.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___355_27994.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27995
                            }  in
                          ((let uu___356_28009 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___356_28009.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___357_28025 = x  in
                            let uu____28026 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___357_28025.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___357_28025.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____28026
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___358_28041 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___358_28041.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____28085 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____28115 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____28115 with
                                  | (p,wopt,e) ->
                                      let uu____28135 = norm_pat env1 p  in
                                      (match uu____28135 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____28190 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____28190
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____28207 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____28207
                      then
                        norm
                          (let uu___359_28212 = cfg1  in
                           {
                             steps =
                               (let uu___360_28215 = cfg1.steps  in
                                {
                                  beta = (uu___360_28215.beta);
                                  iota = (uu___360_28215.iota);
                                  zeta = (uu___360_28215.zeta);
                                  weak = (uu___360_28215.weak);
                                  hnf = (uu___360_28215.hnf);
                                  primops = (uu___360_28215.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___360_28215.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___360_28215.unfold_until);
                                  unfold_only = (uu___360_28215.unfold_only);
                                  unfold_fully =
                                    (uu___360_28215.unfold_fully);
                                  unfold_attr = (uu___360_28215.unfold_attr);
                                  unfold_tac = (uu___360_28215.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___360_28215.pure_subterms_within_computations);
                                  simplify = (uu___360_28215.simplify);
                                  erase_universes =
                                    (uu___360_28215.erase_universes);
                                  allow_unbound_universes =
                                    (uu___360_28215.allow_unbound_universes);
                                  reify_ = (uu___360_28215.reify_);
                                  compress_uvars =
                                    (uu___360_28215.compress_uvars);
                                  no_full_norm =
                                    (uu___360_28215.no_full_norm);
                                  check_no_uvars =
                                    (uu___360_28215.check_no_uvars);
                                  unmeta = (uu___360_28215.unmeta);
                                  unascribe = (uu___360_28215.unascribe);
                                  in_full_norm_request =
                                    (uu___360_28215.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___359_28212.tcenv);
                             debug = (uu___359_28212.debug);
                             delta_level = (uu___359_28212.delta_level);
                             primitive_steps =
                               (uu___359_28212.primitive_steps);
                             strong = (uu___359_28212.strong);
                             memoize_lazy = (uu___359_28212.memoize_lazy);
                             normalize_pure_lets =
                               (uu___359_28212.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____28217 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____28217)
                    in
                 let rec is_cons head1 =
                   let uu____28242 =
                     let uu____28243 = FStar_Syntax_Subst.compress head1  in
                     uu____28243.FStar_Syntax_Syntax.n  in
                   match uu____28242 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____28247) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____28252 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____28253;
                         FStar_Syntax_Syntax.fv_delta = uu____28254;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____28255;
                         FStar_Syntax_Syntax.fv_delta = uu____28256;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____28257);_}
                       -> true
                   | uu____28264 -> false  in
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
                   let uu____28427 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____28427 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____28520 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____28559 ->
                                 let uu____28560 =
                                   let uu____28561 = is_cons head1  in
                                   Prims.op_Negation uu____28561  in
                                 FStar_Util.Inr uu____28560)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____28586 =
                              let uu____28587 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____28587.FStar_Syntax_Syntax.n  in
                            (match uu____28586 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____28605 ->
                                 let uu____28606 =
                                   let uu____28607 = is_cons head1  in
                                   Prims.op_Negation uu____28607  in
                                 FStar_Util.Inr uu____28606))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____28690)::rest_a,(p1,uu____28693)::rest_p) ->
                       let uu____28747 = matches_pat t2 p1  in
                       (match uu____28747 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____28796 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____28916 = matches_pat scrutinee1 p1  in
                       (match uu____28916 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____28956  ->
                                  let uu____28957 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____28958 =
                                    let uu____28959 =
                                      FStar_List.map
                                        (fun uu____28969  ->
                                           match uu____28969 with
                                           | (uu____28974,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____28959
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____28957 uu____28958);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____29006  ->
                                       match uu____29006 with
                                       | (bv,t2) ->
                                           let uu____29029 =
                                             let uu____29036 =
                                               let uu____29039 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____29039
                                                in
                                             let uu____29040 =
                                               let uu____29041 =
                                                 let uu____29072 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____29072, false)
                                                  in
                                               Clos uu____29041  in
                                             (uu____29036, uu____29040)  in
                                           uu____29029 :: env2) env1 s
                                 in
                              let uu____29185 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____29185)))
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
    let uu____29212 =
      let uu____29215 = FStar_ST.op_Bang plugins  in p :: uu____29215  in
    FStar_ST.op_Colon_Equals plugins uu____29212  in
  let retrieve uu____29323 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____29400  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___256_29441  ->
                  match uu___256_29441 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | uu____29445 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____29451 -> d  in
        let uu____29454 = to_fsteps s  in
        let uu____29455 =
          let uu____29456 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____29457 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____29458 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____29459 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____29460 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____29461 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____29462 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____29456;
            primop = uu____29457;
            unfolding = uu____29458;
            b380 = uu____29459;
            wpe = uu____29460;
            norm_delayed = uu____29461;
            print_normalized = uu____29462
          }  in
        let uu____29463 =
          let uu____29466 =
            let uu____29469 = retrieve_plugins ()  in
            FStar_List.append uu____29469 psteps  in
          add_steps built_in_primitive_steps uu____29466  in
        let uu____29472 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____29474 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____29474)
           in
        {
          steps = uu____29454;
          tcenv = e;
          debug = uu____29455;
          delta_level = d1;
          primitive_steps = uu____29463;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____29472
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
            (fun uu____29523  ->
               let uu____29524 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "Starting normalizer for (%s)\n" uu____29524);
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
      fun t  -> let uu____29561 = config s e  in norm_comp uu____29561 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____29578 = config [] env  in norm_universe uu____29578 [] u
  
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
        let uu____29602 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29602  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____29609 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___361_29628 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___361_29628.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___361_29628.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____29635 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____29635
          then
            let ct1 =
              let uu____29637 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____29637 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____29644 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____29644
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___362_29648 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___362_29648.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___362_29648.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___362_29648.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___363_29650 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___363_29650.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___363_29650.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___363_29650.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___363_29650.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___364_29651 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___364_29651.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___364_29651.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____29653 -> c
  
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
        let uu____29671 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29671  in
      let uu____29678 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____29678
      then
        let uu____29679 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____29679 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____29685  ->
                 let uu____29686 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____29686)
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
            ((let uu____29707 =
                let uu____29712 =
                  let uu____29713 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29713
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29712)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____29707);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____29728 = config [AllowUnboundUniverses] env  in
          norm_comp uu____29728 [] c
        with
        | e ->
            ((let uu____29741 =
                let uu____29746 =
                  let uu____29747 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29747
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29746)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____29741);
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
                   let uu____29792 =
                     let uu____29793 =
                       let uu____29800 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____29800)  in
                     FStar_Syntax_Syntax.Tm_refine uu____29793  in
                   mk uu____29792 t01.FStar_Syntax_Syntax.pos
               | uu____29805 -> t2)
          | uu____29806 -> t2  in
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
        let uu____29885 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____29885 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____29922 ->
                 let uu____29931 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____29931 with
                  | (actuals,uu____29941,uu____29942) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____29960 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____29960 with
                         | (binders,args) ->
                             let uu____29971 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____29971
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
      | uu____29985 ->
          let uu____29986 = FStar_Syntax_Util.head_and_args t  in
          (match uu____29986 with
           | (head1,args) ->
               let uu____30029 =
                 let uu____30030 = FStar_Syntax_Subst.compress head1  in
                 uu____30030.FStar_Syntax_Syntax.n  in
               (match uu____30029 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____30051 =
                      let uu____30066 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____30066  in
                    (match uu____30051 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____30104 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___369_30112 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___369_30112.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___369_30112.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___369_30112.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___369_30112.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___369_30112.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___369_30112.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___369_30112.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___369_30112.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___369_30112.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___369_30112.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___369_30112.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___369_30112.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___369_30112.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___369_30112.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___369_30112.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___369_30112.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___369_30112.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___369_30112.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___369_30112.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___369_30112.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___369_30112.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___369_30112.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___369_30112.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___369_30112.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___369_30112.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___369_30112.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___369_30112.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___369_30112.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___369_30112.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___369_30112.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___369_30112.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___369_30112.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___369_30112.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___369_30112.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___369_30112.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___369_30112.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___369_30112.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___369_30112.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____30104 with
                            | (uu____30113,ty,uu____30115) ->
                                eta_expand_with_type env t ty))
                | uu____30116 ->
                    let uu____30117 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___370_30125 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___370_30125.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___370_30125.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___370_30125.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___370_30125.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___370_30125.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___370_30125.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___370_30125.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___370_30125.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___370_30125.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___370_30125.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___370_30125.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___370_30125.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___370_30125.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___370_30125.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___370_30125.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___370_30125.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___370_30125.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___370_30125.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___370_30125.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___370_30125.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___370_30125.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___370_30125.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___370_30125.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___370_30125.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___370_30125.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___370_30125.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___370_30125.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___370_30125.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___370_30125.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___370_30125.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___370_30125.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___370_30125.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___370_30125.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___370_30125.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___370_30125.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___370_30125.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___370_30125.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___370_30125.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____30117 with
                     | (uu____30126,ty,uu____30128) ->
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
      let uu___371_30209 = x  in
      let uu____30210 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___371_30209.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___371_30209.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____30210
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____30213 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____30236 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____30237 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____30238 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____30239 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____30246 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____30247 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____30248 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___372_30282 = rc  in
          let uu____30283 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____30292 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___372_30282.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____30283;
            FStar_Syntax_Syntax.residual_flags = uu____30292
          }  in
        let uu____30295 =
          let uu____30296 =
            let uu____30315 = elim_delayed_subst_binders bs  in
            let uu____30324 = elim_delayed_subst_term t2  in
            let uu____30327 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____30315, uu____30324, uu____30327)  in
          FStar_Syntax_Syntax.Tm_abs uu____30296  in
        mk1 uu____30295
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____30364 =
          let uu____30365 =
            let uu____30380 = elim_delayed_subst_binders bs  in
            let uu____30389 = elim_delayed_subst_comp c  in
            (uu____30380, uu____30389)  in
          FStar_Syntax_Syntax.Tm_arrow uu____30365  in
        mk1 uu____30364
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____30408 =
          let uu____30409 =
            let uu____30416 = elim_bv bv  in
            let uu____30417 = elim_delayed_subst_term phi  in
            (uu____30416, uu____30417)  in
          FStar_Syntax_Syntax.Tm_refine uu____30409  in
        mk1 uu____30408
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____30448 =
          let uu____30449 =
            let uu____30466 = elim_delayed_subst_term t2  in
            let uu____30469 = elim_delayed_subst_args args  in
            (uu____30466, uu____30469)  in
          FStar_Syntax_Syntax.Tm_app uu____30449  in
        mk1 uu____30448
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___373_30541 = p  in
              let uu____30542 =
                let uu____30543 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____30543  in
              {
                FStar_Syntax_Syntax.v = uu____30542;
                FStar_Syntax_Syntax.p =
                  (uu___373_30541.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___374_30545 = p  in
              let uu____30546 =
                let uu____30547 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____30547  in
              {
                FStar_Syntax_Syntax.v = uu____30546;
                FStar_Syntax_Syntax.p =
                  (uu___374_30545.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___375_30554 = p  in
              let uu____30555 =
                let uu____30556 =
                  let uu____30563 = elim_bv x  in
                  let uu____30564 = elim_delayed_subst_term t0  in
                  (uu____30563, uu____30564)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____30556  in
              {
                FStar_Syntax_Syntax.v = uu____30555;
                FStar_Syntax_Syntax.p =
                  (uu___375_30554.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___376_30587 = p  in
              let uu____30588 =
                let uu____30589 =
                  let uu____30602 =
                    FStar_List.map
                      (fun uu____30625  ->
                         match uu____30625 with
                         | (x,b) ->
                             let uu____30638 = elim_pat x  in
                             (uu____30638, b)) pats
                     in
                  (fv, uu____30602)  in
                FStar_Syntax_Syntax.Pat_cons uu____30589  in
              {
                FStar_Syntax_Syntax.v = uu____30588;
                FStar_Syntax_Syntax.p =
                  (uu___376_30587.FStar_Syntax_Syntax.p)
              }
          | uu____30651 -> p  in
        let elim_branch uu____30675 =
          match uu____30675 with
          | (pat,wopt,t3) ->
              let uu____30701 = elim_pat pat  in
              let uu____30704 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____30707 = elim_delayed_subst_term t3  in
              (uu____30701, uu____30704, uu____30707)
           in
        let uu____30712 =
          let uu____30713 =
            let uu____30736 = elim_delayed_subst_term t2  in
            let uu____30739 = FStar_List.map elim_branch branches  in
            (uu____30736, uu____30739)  in
          FStar_Syntax_Syntax.Tm_match uu____30713  in
        mk1 uu____30712
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____30870 =
          match uu____30870 with
          | (tc,topt) ->
              let uu____30905 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____30915 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____30915
                | FStar_Util.Inr c ->
                    let uu____30917 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____30917
                 in
              let uu____30918 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____30905, uu____30918)
           in
        let uu____30927 =
          let uu____30928 =
            let uu____30955 = elim_delayed_subst_term t2  in
            let uu____30958 = elim_ascription a  in
            (uu____30955, uu____30958, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____30928  in
        mk1 uu____30927
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___377_31019 = lb  in
          let uu____31020 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____31023 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___377_31019.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___377_31019.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____31020;
            FStar_Syntax_Syntax.lbeff =
              (uu___377_31019.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____31023;
            FStar_Syntax_Syntax.lbattrs =
              (uu___377_31019.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___377_31019.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____31026 =
          let uu____31027 =
            let uu____31040 =
              let uu____31047 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____31047)  in
            let uu____31056 = elim_delayed_subst_term t2  in
            (uu____31040, uu____31056)  in
          FStar_Syntax_Syntax.Tm_let uu____31027  in
        mk1 uu____31026
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____31100 =
          let uu____31101 =
            let uu____31108 = elim_delayed_subst_term tm  in
            (uu____31108, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____31101  in
        mk1 uu____31100
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____31119 =
          let uu____31120 =
            let uu____31127 = elim_delayed_subst_term t2  in
            let uu____31130 = elim_delayed_subst_meta md  in
            (uu____31127, uu____31130)  in
          FStar_Syntax_Syntax.Tm_meta uu____31120  in
        mk1 uu____31119

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___257_31139  ->
         match uu___257_31139 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____31143 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____31143
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
        let uu____31166 =
          let uu____31167 =
            let uu____31176 = elim_delayed_subst_term t  in
            (uu____31176, uopt)  in
          FStar_Syntax_Syntax.Total uu____31167  in
        mk1 uu____31166
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____31193 =
          let uu____31194 =
            let uu____31203 = elim_delayed_subst_term t  in
            (uu____31203, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____31194  in
        mk1 uu____31193
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___378_31212 = ct  in
          let uu____31213 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____31216 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____31227 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___378_31212.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___378_31212.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____31213;
            FStar_Syntax_Syntax.effect_args = uu____31216;
            FStar_Syntax_Syntax.flags = uu____31227
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___258_31230  ->
    match uu___258_31230 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____31244 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____31244
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____31283 =
          let uu____31290 = elim_delayed_subst_term t  in (m, uu____31290)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____31283
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____31302 =
          let uu____31311 = elim_delayed_subst_term t  in
          (m1, m2, uu____31311)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____31302
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
      (fun uu____31344  ->
         match uu____31344 with
         | (t,q) ->
             let uu____31363 = elim_delayed_subst_term t  in (uu____31363, q))
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
      (fun uu____31391  ->
         match uu____31391 with
         | (x,q) ->
             let uu____31410 =
               let uu___379_31411 = x  in
               let uu____31412 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___379_31411.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___379_31411.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____31412
               }  in
             (uu____31410, q)) bs

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
            | (uu____31518,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____31550,FStar_Util.Inl t) ->
                let uu____31572 =
                  let uu____31579 =
                    let uu____31580 =
                      let uu____31595 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____31595)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____31580  in
                  FStar_Syntax_Syntax.mk uu____31579  in
                uu____31572 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____31611 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____31611 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____31643 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____31716 ->
                    let uu____31717 =
                      let uu____31726 =
                        let uu____31727 = FStar_Syntax_Subst.compress t4  in
                        uu____31727.FStar_Syntax_Syntax.n  in
                      (uu____31726, tc)  in
                    (match uu____31717 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____31756) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____31803) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____31848,FStar_Util.Inl uu____31849) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____31880 -> failwith "Impossible")
                 in
              (match uu____31643 with
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
          let uu____32017 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____32017 with
          | (univ_names1,binders1,tc) ->
              let uu____32091 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____32091)
  
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
          let uu____32144 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____32144 with
          | (univ_names1,binders1,tc) ->
              let uu____32218 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____32218)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____32259 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____32259 with
           | (univ_names1,binders1,typ1) ->
               let uu___380_32299 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___380_32299.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___380_32299.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___380_32299.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___380_32299.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___381_32314 = s  in
          let uu____32315 =
            let uu____32316 =
              let uu____32325 = FStar_List.map (elim_uvars env) sigs  in
              (uu____32325, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____32316  in
          {
            FStar_Syntax_Syntax.sigel = uu____32315;
            FStar_Syntax_Syntax.sigrng =
              (uu___381_32314.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_32314.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_32314.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_32314.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____32342 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32342 with
           | (univ_names1,uu____32366,typ1) ->
               let uu___382_32388 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___382_32388.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___382_32388.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___382_32388.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___382_32388.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____32394 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32394 with
           | (univ_names1,uu____32418,typ1) ->
               let uu___383_32440 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_32440.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_32440.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_32440.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_32440.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____32468 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____32468 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____32493 =
                            let uu____32494 =
                              let uu____32495 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____32495  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____32494
                             in
                          elim_delayed_subst_term uu____32493  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___384_32498 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___384_32498.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___384_32498.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___384_32498.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___384_32498.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___385_32499 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___385_32499.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___385_32499.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___385_32499.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___385_32499.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___386_32505 = s  in
          let uu____32506 =
            let uu____32507 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____32507  in
          {
            FStar_Syntax_Syntax.sigel = uu____32506;
            FStar_Syntax_Syntax.sigrng =
              (uu___386_32505.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___386_32505.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___386_32505.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___386_32505.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____32511 = elim_uvars_aux_t env us [] t  in
          (match uu____32511 with
           | (us1,uu____32535,t1) ->
               let uu___387_32557 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___387_32557.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___387_32557.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___387_32557.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___387_32557.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____32558 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____32560 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____32560 with
           | (univs1,binders,signature) ->
               let uu____32600 =
                 let uu____32605 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____32605 with
                 | (univs_opening,univs2) ->
                     let uu____32628 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____32628)
                  in
               (match uu____32600 with
                | (univs_opening,univs_closing) ->
                    let uu____32631 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____32637 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____32638 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____32637, uu____32638)  in
                    (match uu____32631 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____32664 =
                           match uu____32664 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____32682 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____32682 with
                                | (us1,t1) ->
                                    let uu____32693 =
                                      let uu____32702 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____32713 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____32702, uu____32713)  in
                                    (match uu____32693 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____32742 =
                                           let uu____32751 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____32762 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____32751, uu____32762)  in
                                         (match uu____32742 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____32792 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____32792
                                                 in
                                              let uu____32793 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____32793 with
                                               | (uu____32820,uu____32821,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____32844 =
                                                       let uu____32845 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____32845
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____32844
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____32854 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____32854 with
                           | (uu____32873,uu____32874,t1) -> t1  in
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
                             | uu____32950 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____32977 =
                               let uu____32978 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____32978.FStar_Syntax_Syntax.n  in
                             match uu____32977 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____33037 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____33070 =
                               let uu____33071 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____33071.FStar_Syntax_Syntax.n  in
                             match uu____33070 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____33094) ->
                                 let uu____33119 = destruct_action_body body
                                    in
                                 (match uu____33119 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____33168 ->
                                 let uu____33169 = destruct_action_body t  in
                                 (match uu____33169 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____33224 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____33224 with
                           | (action_univs,t) ->
                               let uu____33233 = destruct_action_typ_templ t
                                  in
                               (match uu____33233 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___388_33280 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___388_33280.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___388_33280.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___389_33282 = ed  in
                           let uu____33283 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____33284 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____33285 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____33286 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____33287 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____33288 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____33289 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____33290 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____33291 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____33292 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____33293 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____33294 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____33295 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____33296 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___389_33282.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___389_33282.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____33283;
                             FStar_Syntax_Syntax.bind_wp = uu____33284;
                             FStar_Syntax_Syntax.if_then_else = uu____33285;
                             FStar_Syntax_Syntax.ite_wp = uu____33286;
                             FStar_Syntax_Syntax.stronger = uu____33287;
                             FStar_Syntax_Syntax.close_wp = uu____33288;
                             FStar_Syntax_Syntax.assert_p = uu____33289;
                             FStar_Syntax_Syntax.assume_p = uu____33290;
                             FStar_Syntax_Syntax.null_wp = uu____33291;
                             FStar_Syntax_Syntax.trivial = uu____33292;
                             FStar_Syntax_Syntax.repr = uu____33293;
                             FStar_Syntax_Syntax.return_repr = uu____33294;
                             FStar_Syntax_Syntax.bind_repr = uu____33295;
                             FStar_Syntax_Syntax.actions = uu____33296;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___389_33282.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___390_33299 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___390_33299.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___390_33299.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___390_33299.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___390_33299.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___259_33320 =
            match uu___259_33320 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____33351 = elim_uvars_aux_t env us [] t  in
                (match uu____33351 with
                 | (us1,uu____33383,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___391_33414 = sub_eff  in
            let uu____33415 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____33418 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___391_33414.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___391_33414.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____33415;
              FStar_Syntax_Syntax.lift = uu____33418
            }  in
          let uu___392_33421 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___392_33421.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___392_33421.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___392_33421.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___392_33421.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____33431 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____33431 with
           | (univ_names1,binders1,comp1) ->
               let uu___393_33471 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___393_33471.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___393_33471.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___393_33471.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___393_33471.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____33474 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____33475 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  