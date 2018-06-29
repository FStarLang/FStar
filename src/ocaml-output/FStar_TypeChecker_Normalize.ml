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
  
let (steps_to_string : fsteps -> Prims.string) =
  fun steps  ->
    let uu____1474 =
      let uu____1477 =
        let uu____1480 =
          let uu____1481 = FStar_Util.string_of_bool steps.beta  in
          FStar_Util.format1 "    beta = %s;" uu____1481  in
        let uu____1482 =
          let uu____1485 =
            let uu____1486 = FStar_Util.string_of_bool steps.iota  in
            FStar_Util.format1 "    iota = %s;" uu____1486  in
          let uu____1487 =
            let uu____1490 =
              let uu____1491 = FStar_Util.string_of_bool steps.zeta  in
              FStar_Util.format1 "    zeta = %s;" uu____1491  in
            let uu____1492 =
              let uu____1495 =
                let uu____1496 = FStar_Util.string_of_bool steps.weak  in
                FStar_Util.format1 "    weak = %s;" uu____1496  in
              let uu____1497 =
                let uu____1500 =
                  let uu____1501 = FStar_Util.string_of_bool steps.hnf  in
                  FStar_Util.format1 "    hnf = %s;" uu____1501  in
                let uu____1502 =
                  let uu____1505 =
                    let uu____1506 = FStar_Util.string_of_bool steps.primops
                       in
                    FStar_Util.format1 "    primops = %s;" uu____1506  in
                  let uu____1507 =
                    let uu____1510 =
                      let uu____1511 =
                        FStar_Util.string_of_bool
                          steps.do_not_unfold_pure_lets
                         in
                      FStar_Util.format1 "    do_not_unfold_pure_lets = %s;"
                        uu____1511
                       in
                    let uu____1512 =
                      let uu____1515 =
                        let uu____1516 =
                          FStar_Util.string_of_bool steps.unfold_tac  in
                        FStar_Util.format1 "    unfold_tac = %s;" uu____1516
                         in
                      let uu____1517 =
                        let uu____1520 =
                          let uu____1521 =
                            FStar_Util.string_of_bool
                              steps.pure_subterms_within_computations
                             in
                          FStar_Util.format1
                            "    pure_subterms_within_computations = %s;"
                            uu____1521
                           in
                        let uu____1522 =
                          let uu____1525 =
                            let uu____1526 =
                              FStar_Util.string_of_bool steps.simplify  in
                            FStar_Util.format1 "    simplify = %s;"
                              uu____1526
                             in
                          let uu____1527 =
                            let uu____1530 =
                              let uu____1531 =
                                FStar_Util.string_of_bool
                                  steps.erase_universes
                                 in
                              FStar_Util.format1 "    erase_universes = %s;"
                                uu____1531
                               in
                            let uu____1532 =
                              let uu____1535 =
                                let uu____1536 =
                                  FStar_Util.string_of_bool
                                    steps.allow_unbound_universes
                                   in
                                FStar_Util.format1
                                  "    allow_unbound_universes = %s;"
                                  uu____1536
                                 in
                              let uu____1537 =
                                let uu____1540 =
                                  let uu____1541 =
                                    FStar_Util.string_of_bool steps.reify_
                                     in
                                  FStar_Util.format1 "    reify_ = %s;"
                                    uu____1541
                                   in
                                let uu____1542 =
                                  let uu____1545 =
                                    let uu____1546 =
                                      FStar_Util.string_of_bool
                                        steps.compress_uvars
                                       in
                                    FStar_Util.format1
                                      "    compress_uvars = %s;" uu____1546
                                     in
                                  let uu____1547 =
                                    let uu____1550 =
                                      let uu____1551 =
                                        FStar_Util.string_of_bool
                                          steps.no_full_norm
                                         in
                                      FStar_Util.format1
                                        "    no_full_norm = %s;" uu____1551
                                       in
                                    let uu____1552 =
                                      let uu____1555 =
                                        let uu____1556 =
                                          FStar_Util.string_of_bool
                                            steps.check_no_uvars
                                           in
                                        FStar_Util.format1
                                          "    check_no_uvars = %s;"
                                          uu____1556
                                         in
                                      let uu____1557 =
                                        let uu____1560 =
                                          let uu____1561 =
                                            FStar_Util.string_of_bool
                                              steps.unmeta
                                             in
                                          FStar_Util.format1
                                            "    unmeta = %s;" uu____1561
                                           in
                                        let uu____1562 =
                                          let uu____1565 =
                                            let uu____1566 =
                                              FStar_Util.string_of_bool
                                                steps.unascribe
                                               in
                                            FStar_Util.format1
                                              "    unascribe = %s;"
                                              uu____1566
                                             in
                                          let uu____1567 =
                                            let uu____1570 =
                                              let uu____1571 =
                                                FStar_Util.string_of_bool
                                                  steps.in_full_norm_request
                                                 in
                                              FStar_Util.format1
                                                "    in_full_norm_request = %s;"
                                                uu____1571
                                               in
                                            let uu____1572 =
                                              let uu____1575 =
                                                let uu____1576 =
                                                  FStar_Util.string_of_bool
                                                    steps.weakly_reduce_scrutinee
                                                   in
                                                FStar_Util.format1
                                                  "    weakly_reduce_scrutinee = %s;"
                                                  uu____1576
                                                 in
                                              [uu____1575; "  }"]  in
                                            uu____1570 :: uu____1572  in
                                          uu____1565 :: uu____1567  in
                                        uu____1560 :: uu____1562  in
                                      uu____1555 :: uu____1557  in
                                    uu____1550 :: uu____1552  in
                                  uu____1545 :: uu____1547  in
                                uu____1540 :: uu____1542  in
                              uu____1535 :: uu____1537  in
                            uu____1530 :: uu____1532  in
                          uu____1525 :: uu____1527  in
                        uu____1520 :: uu____1522  in
                      uu____1515 :: uu____1517  in
                    uu____1510 :: uu____1512  in
                  uu____1505 :: uu____1507  in
                uu____1500 :: uu____1502  in
              uu____1495 :: uu____1497  in
            uu____1490 :: uu____1492  in
          uu____1485 :: uu____1487  in
        uu____1480 :: uu____1482  in
      "{" :: uu____1477  in
    FStar_String.concat "\n" uu____1474
  
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
      let add_opt x uu___241_1611 =
        match uu___241_1611 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___260_1631 = fs  in
          {
            beta = true;
            iota = (uu___260_1631.iota);
            zeta = (uu___260_1631.zeta);
            weak = (uu___260_1631.weak);
            hnf = (uu___260_1631.hnf);
            primops = (uu___260_1631.primops);
            do_not_unfold_pure_lets = (uu___260_1631.do_not_unfold_pure_lets);
            unfold_until = (uu___260_1631.unfold_until);
            unfold_only = (uu___260_1631.unfold_only);
            unfold_fully = (uu___260_1631.unfold_fully);
            unfold_attr = (uu___260_1631.unfold_attr);
            unfold_tac = (uu___260_1631.unfold_tac);
            pure_subterms_within_computations =
              (uu___260_1631.pure_subterms_within_computations);
            simplify = (uu___260_1631.simplify);
            erase_universes = (uu___260_1631.erase_universes);
            allow_unbound_universes = (uu___260_1631.allow_unbound_universes);
            reify_ = (uu___260_1631.reify_);
            compress_uvars = (uu___260_1631.compress_uvars);
            no_full_norm = (uu___260_1631.no_full_norm);
            check_no_uvars = (uu___260_1631.check_no_uvars);
            unmeta = (uu___260_1631.unmeta);
            unascribe = (uu___260_1631.unascribe);
            in_full_norm_request = (uu___260_1631.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___260_1631.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___261_1632 = fs  in
          {
            beta = (uu___261_1632.beta);
            iota = true;
            zeta = (uu___261_1632.zeta);
            weak = (uu___261_1632.weak);
            hnf = (uu___261_1632.hnf);
            primops = (uu___261_1632.primops);
            do_not_unfold_pure_lets = (uu___261_1632.do_not_unfold_pure_lets);
            unfold_until = (uu___261_1632.unfold_until);
            unfold_only = (uu___261_1632.unfold_only);
            unfold_fully = (uu___261_1632.unfold_fully);
            unfold_attr = (uu___261_1632.unfold_attr);
            unfold_tac = (uu___261_1632.unfold_tac);
            pure_subterms_within_computations =
              (uu___261_1632.pure_subterms_within_computations);
            simplify = (uu___261_1632.simplify);
            erase_universes = (uu___261_1632.erase_universes);
            allow_unbound_universes = (uu___261_1632.allow_unbound_universes);
            reify_ = (uu___261_1632.reify_);
            compress_uvars = (uu___261_1632.compress_uvars);
            no_full_norm = (uu___261_1632.no_full_norm);
            check_no_uvars = (uu___261_1632.check_no_uvars);
            unmeta = (uu___261_1632.unmeta);
            unascribe = (uu___261_1632.unascribe);
            in_full_norm_request = (uu___261_1632.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___261_1632.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___262_1633 = fs  in
          {
            beta = (uu___262_1633.beta);
            iota = (uu___262_1633.iota);
            zeta = true;
            weak = (uu___262_1633.weak);
            hnf = (uu___262_1633.hnf);
            primops = (uu___262_1633.primops);
            do_not_unfold_pure_lets = (uu___262_1633.do_not_unfold_pure_lets);
            unfold_until = (uu___262_1633.unfold_until);
            unfold_only = (uu___262_1633.unfold_only);
            unfold_fully = (uu___262_1633.unfold_fully);
            unfold_attr = (uu___262_1633.unfold_attr);
            unfold_tac = (uu___262_1633.unfold_tac);
            pure_subterms_within_computations =
              (uu___262_1633.pure_subterms_within_computations);
            simplify = (uu___262_1633.simplify);
            erase_universes = (uu___262_1633.erase_universes);
            allow_unbound_universes = (uu___262_1633.allow_unbound_universes);
            reify_ = (uu___262_1633.reify_);
            compress_uvars = (uu___262_1633.compress_uvars);
            no_full_norm = (uu___262_1633.no_full_norm);
            check_no_uvars = (uu___262_1633.check_no_uvars);
            unmeta = (uu___262_1633.unmeta);
            unascribe = (uu___262_1633.unascribe);
            in_full_norm_request = (uu___262_1633.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___262_1633.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___263_1634 = fs  in
          {
            beta = false;
            iota = (uu___263_1634.iota);
            zeta = (uu___263_1634.zeta);
            weak = (uu___263_1634.weak);
            hnf = (uu___263_1634.hnf);
            primops = (uu___263_1634.primops);
            do_not_unfold_pure_lets = (uu___263_1634.do_not_unfold_pure_lets);
            unfold_until = (uu___263_1634.unfold_until);
            unfold_only = (uu___263_1634.unfold_only);
            unfold_fully = (uu___263_1634.unfold_fully);
            unfold_attr = (uu___263_1634.unfold_attr);
            unfold_tac = (uu___263_1634.unfold_tac);
            pure_subterms_within_computations =
              (uu___263_1634.pure_subterms_within_computations);
            simplify = (uu___263_1634.simplify);
            erase_universes = (uu___263_1634.erase_universes);
            allow_unbound_universes = (uu___263_1634.allow_unbound_universes);
            reify_ = (uu___263_1634.reify_);
            compress_uvars = (uu___263_1634.compress_uvars);
            no_full_norm = (uu___263_1634.no_full_norm);
            check_no_uvars = (uu___263_1634.check_no_uvars);
            unmeta = (uu___263_1634.unmeta);
            unascribe = (uu___263_1634.unascribe);
            in_full_norm_request = (uu___263_1634.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___263_1634.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___264_1635 = fs  in
          {
            beta = (uu___264_1635.beta);
            iota = false;
            zeta = (uu___264_1635.zeta);
            weak = (uu___264_1635.weak);
            hnf = (uu___264_1635.hnf);
            primops = (uu___264_1635.primops);
            do_not_unfold_pure_lets = (uu___264_1635.do_not_unfold_pure_lets);
            unfold_until = (uu___264_1635.unfold_until);
            unfold_only = (uu___264_1635.unfold_only);
            unfold_fully = (uu___264_1635.unfold_fully);
            unfold_attr = (uu___264_1635.unfold_attr);
            unfold_tac = (uu___264_1635.unfold_tac);
            pure_subterms_within_computations =
              (uu___264_1635.pure_subterms_within_computations);
            simplify = (uu___264_1635.simplify);
            erase_universes = (uu___264_1635.erase_universes);
            allow_unbound_universes = (uu___264_1635.allow_unbound_universes);
            reify_ = (uu___264_1635.reify_);
            compress_uvars = (uu___264_1635.compress_uvars);
            no_full_norm = (uu___264_1635.no_full_norm);
            check_no_uvars = (uu___264_1635.check_no_uvars);
            unmeta = (uu___264_1635.unmeta);
            unascribe = (uu___264_1635.unascribe);
            in_full_norm_request = (uu___264_1635.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___264_1635.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___265_1636 = fs  in
          {
            beta = (uu___265_1636.beta);
            iota = (uu___265_1636.iota);
            zeta = false;
            weak = (uu___265_1636.weak);
            hnf = (uu___265_1636.hnf);
            primops = (uu___265_1636.primops);
            do_not_unfold_pure_lets = (uu___265_1636.do_not_unfold_pure_lets);
            unfold_until = (uu___265_1636.unfold_until);
            unfold_only = (uu___265_1636.unfold_only);
            unfold_fully = (uu___265_1636.unfold_fully);
            unfold_attr = (uu___265_1636.unfold_attr);
            unfold_tac = (uu___265_1636.unfold_tac);
            pure_subterms_within_computations =
              (uu___265_1636.pure_subterms_within_computations);
            simplify = (uu___265_1636.simplify);
            erase_universes = (uu___265_1636.erase_universes);
            allow_unbound_universes = (uu___265_1636.allow_unbound_universes);
            reify_ = (uu___265_1636.reify_);
            compress_uvars = (uu___265_1636.compress_uvars);
            no_full_norm = (uu___265_1636.no_full_norm);
            check_no_uvars = (uu___265_1636.check_no_uvars);
            unmeta = (uu___265_1636.unmeta);
            unascribe = (uu___265_1636.unascribe);
            in_full_norm_request = (uu___265_1636.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___265_1636.weakly_reduce_scrutinee)
          }
      | Exclude uu____1637 -> failwith "Bad exclude"
      | Weak  ->
          let uu___266_1638 = fs  in
          {
            beta = (uu___266_1638.beta);
            iota = (uu___266_1638.iota);
            zeta = (uu___266_1638.zeta);
            weak = true;
            hnf = (uu___266_1638.hnf);
            primops = (uu___266_1638.primops);
            do_not_unfold_pure_lets = (uu___266_1638.do_not_unfold_pure_lets);
            unfold_until = (uu___266_1638.unfold_until);
            unfold_only = (uu___266_1638.unfold_only);
            unfold_fully = (uu___266_1638.unfold_fully);
            unfold_attr = (uu___266_1638.unfold_attr);
            unfold_tac = (uu___266_1638.unfold_tac);
            pure_subterms_within_computations =
              (uu___266_1638.pure_subterms_within_computations);
            simplify = (uu___266_1638.simplify);
            erase_universes = (uu___266_1638.erase_universes);
            allow_unbound_universes = (uu___266_1638.allow_unbound_universes);
            reify_ = (uu___266_1638.reify_);
            compress_uvars = (uu___266_1638.compress_uvars);
            no_full_norm = (uu___266_1638.no_full_norm);
            check_no_uvars = (uu___266_1638.check_no_uvars);
            unmeta = (uu___266_1638.unmeta);
            unascribe = (uu___266_1638.unascribe);
            in_full_norm_request = (uu___266_1638.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___266_1638.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___267_1639 = fs  in
          {
            beta = (uu___267_1639.beta);
            iota = (uu___267_1639.iota);
            zeta = (uu___267_1639.zeta);
            weak = (uu___267_1639.weak);
            hnf = true;
            primops = (uu___267_1639.primops);
            do_not_unfold_pure_lets = (uu___267_1639.do_not_unfold_pure_lets);
            unfold_until = (uu___267_1639.unfold_until);
            unfold_only = (uu___267_1639.unfold_only);
            unfold_fully = (uu___267_1639.unfold_fully);
            unfold_attr = (uu___267_1639.unfold_attr);
            unfold_tac = (uu___267_1639.unfold_tac);
            pure_subterms_within_computations =
              (uu___267_1639.pure_subterms_within_computations);
            simplify = (uu___267_1639.simplify);
            erase_universes = (uu___267_1639.erase_universes);
            allow_unbound_universes = (uu___267_1639.allow_unbound_universes);
            reify_ = (uu___267_1639.reify_);
            compress_uvars = (uu___267_1639.compress_uvars);
            no_full_norm = (uu___267_1639.no_full_norm);
            check_no_uvars = (uu___267_1639.check_no_uvars);
            unmeta = (uu___267_1639.unmeta);
            unascribe = (uu___267_1639.unascribe);
            in_full_norm_request = (uu___267_1639.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___267_1639.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___268_1640 = fs  in
          {
            beta = (uu___268_1640.beta);
            iota = (uu___268_1640.iota);
            zeta = (uu___268_1640.zeta);
            weak = (uu___268_1640.weak);
            hnf = (uu___268_1640.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___268_1640.do_not_unfold_pure_lets);
            unfold_until = (uu___268_1640.unfold_until);
            unfold_only = (uu___268_1640.unfold_only);
            unfold_fully = (uu___268_1640.unfold_fully);
            unfold_attr = (uu___268_1640.unfold_attr);
            unfold_tac = (uu___268_1640.unfold_tac);
            pure_subterms_within_computations =
              (uu___268_1640.pure_subterms_within_computations);
            simplify = (uu___268_1640.simplify);
            erase_universes = (uu___268_1640.erase_universes);
            allow_unbound_universes = (uu___268_1640.allow_unbound_universes);
            reify_ = (uu___268_1640.reify_);
            compress_uvars = (uu___268_1640.compress_uvars);
            no_full_norm = (uu___268_1640.no_full_norm);
            check_no_uvars = (uu___268_1640.check_no_uvars);
            unmeta = (uu___268_1640.unmeta);
            unascribe = (uu___268_1640.unascribe);
            in_full_norm_request = (uu___268_1640.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___268_1640.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___269_1641 = fs  in
          {
            beta = (uu___269_1641.beta);
            iota = (uu___269_1641.iota);
            zeta = (uu___269_1641.zeta);
            weak = (uu___269_1641.weak);
            hnf = (uu___269_1641.hnf);
            primops = (uu___269_1641.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___269_1641.unfold_until);
            unfold_only = (uu___269_1641.unfold_only);
            unfold_fully = (uu___269_1641.unfold_fully);
            unfold_attr = (uu___269_1641.unfold_attr);
            unfold_tac = (uu___269_1641.unfold_tac);
            pure_subterms_within_computations =
              (uu___269_1641.pure_subterms_within_computations);
            simplify = (uu___269_1641.simplify);
            erase_universes = (uu___269_1641.erase_universes);
            allow_unbound_universes = (uu___269_1641.allow_unbound_universes);
            reify_ = (uu___269_1641.reify_);
            compress_uvars = (uu___269_1641.compress_uvars);
            no_full_norm = (uu___269_1641.no_full_norm);
            check_no_uvars = (uu___269_1641.check_no_uvars);
            unmeta = (uu___269_1641.unmeta);
            unascribe = (uu___269_1641.unascribe);
            in_full_norm_request = (uu___269_1641.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___269_1641.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___270_1643 = fs  in
          {
            beta = (uu___270_1643.beta);
            iota = (uu___270_1643.iota);
            zeta = (uu___270_1643.zeta);
            weak = (uu___270_1643.weak);
            hnf = (uu___270_1643.hnf);
            primops = (uu___270_1643.primops);
            do_not_unfold_pure_lets = (uu___270_1643.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___270_1643.unfold_only);
            unfold_fully = (uu___270_1643.unfold_fully);
            unfold_attr = (uu___270_1643.unfold_attr);
            unfold_tac = (uu___270_1643.unfold_tac);
            pure_subterms_within_computations =
              (uu___270_1643.pure_subterms_within_computations);
            simplify = (uu___270_1643.simplify);
            erase_universes = (uu___270_1643.erase_universes);
            allow_unbound_universes = (uu___270_1643.allow_unbound_universes);
            reify_ = (uu___270_1643.reify_);
            compress_uvars = (uu___270_1643.compress_uvars);
            no_full_norm = (uu___270_1643.no_full_norm);
            check_no_uvars = (uu___270_1643.check_no_uvars);
            unmeta = (uu___270_1643.unmeta);
            unascribe = (uu___270_1643.unascribe);
            in_full_norm_request = (uu___270_1643.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___270_1643.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___271_1647 = fs  in
          {
            beta = (uu___271_1647.beta);
            iota = (uu___271_1647.iota);
            zeta = (uu___271_1647.zeta);
            weak = (uu___271_1647.weak);
            hnf = (uu___271_1647.hnf);
            primops = (uu___271_1647.primops);
            do_not_unfold_pure_lets = (uu___271_1647.do_not_unfold_pure_lets);
            unfold_until = (uu___271_1647.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___271_1647.unfold_fully);
            unfold_attr = (uu___271_1647.unfold_attr);
            unfold_tac = (uu___271_1647.unfold_tac);
            pure_subterms_within_computations =
              (uu___271_1647.pure_subterms_within_computations);
            simplify = (uu___271_1647.simplify);
            erase_universes = (uu___271_1647.erase_universes);
            allow_unbound_universes = (uu___271_1647.allow_unbound_universes);
            reify_ = (uu___271_1647.reify_);
            compress_uvars = (uu___271_1647.compress_uvars);
            no_full_norm = (uu___271_1647.no_full_norm);
            check_no_uvars = (uu___271_1647.check_no_uvars);
            unmeta = (uu___271_1647.unmeta);
            unascribe = (uu___271_1647.unascribe);
            in_full_norm_request = (uu___271_1647.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___271_1647.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___272_1653 = fs  in
          {
            beta = (uu___272_1653.beta);
            iota = (uu___272_1653.iota);
            zeta = (uu___272_1653.zeta);
            weak = (uu___272_1653.weak);
            hnf = (uu___272_1653.hnf);
            primops = (uu___272_1653.primops);
            do_not_unfold_pure_lets = (uu___272_1653.do_not_unfold_pure_lets);
            unfold_until = (uu___272_1653.unfold_until);
            unfold_only = (uu___272_1653.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___272_1653.unfold_attr);
            unfold_tac = (uu___272_1653.unfold_tac);
            pure_subterms_within_computations =
              (uu___272_1653.pure_subterms_within_computations);
            simplify = (uu___272_1653.simplify);
            erase_universes = (uu___272_1653.erase_universes);
            allow_unbound_universes = (uu___272_1653.allow_unbound_universes);
            reify_ = (uu___272_1653.reify_);
            compress_uvars = (uu___272_1653.compress_uvars);
            no_full_norm = (uu___272_1653.no_full_norm);
            check_no_uvars = (uu___272_1653.check_no_uvars);
            unmeta = (uu___272_1653.unmeta);
            unascribe = (uu___272_1653.unascribe);
            in_full_norm_request = (uu___272_1653.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___272_1653.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___273_1657 = fs  in
          {
            beta = (uu___273_1657.beta);
            iota = (uu___273_1657.iota);
            zeta = (uu___273_1657.zeta);
            weak = (uu___273_1657.weak);
            hnf = (uu___273_1657.hnf);
            primops = (uu___273_1657.primops);
            do_not_unfold_pure_lets = (uu___273_1657.do_not_unfold_pure_lets);
            unfold_until = (uu___273_1657.unfold_until);
            unfold_only = (uu___273_1657.unfold_only);
            unfold_fully = (uu___273_1657.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___273_1657.unfold_tac);
            pure_subterms_within_computations =
              (uu___273_1657.pure_subterms_within_computations);
            simplify = (uu___273_1657.simplify);
            erase_universes = (uu___273_1657.erase_universes);
            allow_unbound_universes = (uu___273_1657.allow_unbound_universes);
            reify_ = (uu___273_1657.reify_);
            compress_uvars = (uu___273_1657.compress_uvars);
            no_full_norm = (uu___273_1657.no_full_norm);
            check_no_uvars = (uu___273_1657.check_no_uvars);
            unmeta = (uu___273_1657.unmeta);
            unascribe = (uu___273_1657.unascribe);
            in_full_norm_request = (uu___273_1657.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___273_1657.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___274_1658 = fs  in
          {
            beta = (uu___274_1658.beta);
            iota = (uu___274_1658.iota);
            zeta = (uu___274_1658.zeta);
            weak = (uu___274_1658.weak);
            hnf = (uu___274_1658.hnf);
            primops = (uu___274_1658.primops);
            do_not_unfold_pure_lets = (uu___274_1658.do_not_unfold_pure_lets);
            unfold_until = (uu___274_1658.unfold_until);
            unfold_only = (uu___274_1658.unfold_only);
            unfold_fully = (uu___274_1658.unfold_fully);
            unfold_attr = (uu___274_1658.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___274_1658.pure_subterms_within_computations);
            simplify = (uu___274_1658.simplify);
            erase_universes = (uu___274_1658.erase_universes);
            allow_unbound_universes = (uu___274_1658.allow_unbound_universes);
            reify_ = (uu___274_1658.reify_);
            compress_uvars = (uu___274_1658.compress_uvars);
            no_full_norm = (uu___274_1658.no_full_norm);
            check_no_uvars = (uu___274_1658.check_no_uvars);
            unmeta = (uu___274_1658.unmeta);
            unascribe = (uu___274_1658.unascribe);
            in_full_norm_request = (uu___274_1658.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___274_1658.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___275_1659 = fs  in
          {
            beta = (uu___275_1659.beta);
            iota = (uu___275_1659.iota);
            zeta = (uu___275_1659.zeta);
            weak = (uu___275_1659.weak);
            hnf = (uu___275_1659.hnf);
            primops = (uu___275_1659.primops);
            do_not_unfold_pure_lets = (uu___275_1659.do_not_unfold_pure_lets);
            unfold_until = (uu___275_1659.unfold_until);
            unfold_only = (uu___275_1659.unfold_only);
            unfold_fully = (uu___275_1659.unfold_fully);
            unfold_attr = (uu___275_1659.unfold_attr);
            unfold_tac = (uu___275_1659.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___275_1659.simplify);
            erase_universes = (uu___275_1659.erase_universes);
            allow_unbound_universes = (uu___275_1659.allow_unbound_universes);
            reify_ = (uu___275_1659.reify_);
            compress_uvars = (uu___275_1659.compress_uvars);
            no_full_norm = (uu___275_1659.no_full_norm);
            check_no_uvars = (uu___275_1659.check_no_uvars);
            unmeta = (uu___275_1659.unmeta);
            unascribe = (uu___275_1659.unascribe);
            in_full_norm_request = (uu___275_1659.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___275_1659.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___276_1660 = fs  in
          {
            beta = (uu___276_1660.beta);
            iota = (uu___276_1660.iota);
            zeta = (uu___276_1660.zeta);
            weak = (uu___276_1660.weak);
            hnf = (uu___276_1660.hnf);
            primops = (uu___276_1660.primops);
            do_not_unfold_pure_lets = (uu___276_1660.do_not_unfold_pure_lets);
            unfold_until = (uu___276_1660.unfold_until);
            unfold_only = (uu___276_1660.unfold_only);
            unfold_fully = (uu___276_1660.unfold_fully);
            unfold_attr = (uu___276_1660.unfold_attr);
            unfold_tac = (uu___276_1660.unfold_tac);
            pure_subterms_within_computations =
              (uu___276_1660.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___276_1660.erase_universes);
            allow_unbound_universes = (uu___276_1660.allow_unbound_universes);
            reify_ = (uu___276_1660.reify_);
            compress_uvars = (uu___276_1660.compress_uvars);
            no_full_norm = (uu___276_1660.no_full_norm);
            check_no_uvars = (uu___276_1660.check_no_uvars);
            unmeta = (uu___276_1660.unmeta);
            unascribe = (uu___276_1660.unascribe);
            in_full_norm_request = (uu___276_1660.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___276_1660.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___277_1661 = fs  in
          {
            beta = (uu___277_1661.beta);
            iota = (uu___277_1661.iota);
            zeta = (uu___277_1661.zeta);
            weak = (uu___277_1661.weak);
            hnf = (uu___277_1661.hnf);
            primops = (uu___277_1661.primops);
            do_not_unfold_pure_lets = (uu___277_1661.do_not_unfold_pure_lets);
            unfold_until = (uu___277_1661.unfold_until);
            unfold_only = (uu___277_1661.unfold_only);
            unfold_fully = (uu___277_1661.unfold_fully);
            unfold_attr = (uu___277_1661.unfold_attr);
            unfold_tac = (uu___277_1661.unfold_tac);
            pure_subterms_within_computations =
              (uu___277_1661.pure_subterms_within_computations);
            simplify = (uu___277_1661.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___277_1661.allow_unbound_universes);
            reify_ = (uu___277_1661.reify_);
            compress_uvars = (uu___277_1661.compress_uvars);
            no_full_norm = (uu___277_1661.no_full_norm);
            check_no_uvars = (uu___277_1661.check_no_uvars);
            unmeta = (uu___277_1661.unmeta);
            unascribe = (uu___277_1661.unascribe);
            in_full_norm_request = (uu___277_1661.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___277_1661.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___278_1662 = fs  in
          {
            beta = (uu___278_1662.beta);
            iota = (uu___278_1662.iota);
            zeta = (uu___278_1662.zeta);
            weak = (uu___278_1662.weak);
            hnf = (uu___278_1662.hnf);
            primops = (uu___278_1662.primops);
            do_not_unfold_pure_lets = (uu___278_1662.do_not_unfold_pure_lets);
            unfold_until = (uu___278_1662.unfold_until);
            unfold_only = (uu___278_1662.unfold_only);
            unfold_fully = (uu___278_1662.unfold_fully);
            unfold_attr = (uu___278_1662.unfold_attr);
            unfold_tac = (uu___278_1662.unfold_tac);
            pure_subterms_within_computations =
              (uu___278_1662.pure_subterms_within_computations);
            simplify = (uu___278_1662.simplify);
            erase_universes = (uu___278_1662.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___278_1662.reify_);
            compress_uvars = (uu___278_1662.compress_uvars);
            no_full_norm = (uu___278_1662.no_full_norm);
            check_no_uvars = (uu___278_1662.check_no_uvars);
            unmeta = (uu___278_1662.unmeta);
            unascribe = (uu___278_1662.unascribe);
            in_full_norm_request = (uu___278_1662.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___278_1662.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___279_1663 = fs  in
          {
            beta = (uu___279_1663.beta);
            iota = (uu___279_1663.iota);
            zeta = (uu___279_1663.zeta);
            weak = (uu___279_1663.weak);
            hnf = (uu___279_1663.hnf);
            primops = (uu___279_1663.primops);
            do_not_unfold_pure_lets = (uu___279_1663.do_not_unfold_pure_lets);
            unfold_until = (uu___279_1663.unfold_until);
            unfold_only = (uu___279_1663.unfold_only);
            unfold_fully = (uu___279_1663.unfold_fully);
            unfold_attr = (uu___279_1663.unfold_attr);
            unfold_tac = (uu___279_1663.unfold_tac);
            pure_subterms_within_computations =
              (uu___279_1663.pure_subterms_within_computations);
            simplify = (uu___279_1663.simplify);
            erase_universes = (uu___279_1663.erase_universes);
            allow_unbound_universes = (uu___279_1663.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___279_1663.compress_uvars);
            no_full_norm = (uu___279_1663.no_full_norm);
            check_no_uvars = (uu___279_1663.check_no_uvars);
            unmeta = (uu___279_1663.unmeta);
            unascribe = (uu___279_1663.unascribe);
            in_full_norm_request = (uu___279_1663.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___279_1663.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___280_1664 = fs  in
          {
            beta = (uu___280_1664.beta);
            iota = (uu___280_1664.iota);
            zeta = (uu___280_1664.zeta);
            weak = (uu___280_1664.weak);
            hnf = (uu___280_1664.hnf);
            primops = (uu___280_1664.primops);
            do_not_unfold_pure_lets = (uu___280_1664.do_not_unfold_pure_lets);
            unfold_until = (uu___280_1664.unfold_until);
            unfold_only = (uu___280_1664.unfold_only);
            unfold_fully = (uu___280_1664.unfold_fully);
            unfold_attr = (uu___280_1664.unfold_attr);
            unfold_tac = (uu___280_1664.unfold_tac);
            pure_subterms_within_computations =
              (uu___280_1664.pure_subterms_within_computations);
            simplify = (uu___280_1664.simplify);
            erase_universes = (uu___280_1664.erase_universes);
            allow_unbound_universes = (uu___280_1664.allow_unbound_universes);
            reify_ = (uu___280_1664.reify_);
            compress_uvars = true;
            no_full_norm = (uu___280_1664.no_full_norm);
            check_no_uvars = (uu___280_1664.check_no_uvars);
            unmeta = (uu___280_1664.unmeta);
            unascribe = (uu___280_1664.unascribe);
            in_full_norm_request = (uu___280_1664.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___280_1664.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___281_1665 = fs  in
          {
            beta = (uu___281_1665.beta);
            iota = (uu___281_1665.iota);
            zeta = (uu___281_1665.zeta);
            weak = (uu___281_1665.weak);
            hnf = (uu___281_1665.hnf);
            primops = (uu___281_1665.primops);
            do_not_unfold_pure_lets = (uu___281_1665.do_not_unfold_pure_lets);
            unfold_until = (uu___281_1665.unfold_until);
            unfold_only = (uu___281_1665.unfold_only);
            unfold_fully = (uu___281_1665.unfold_fully);
            unfold_attr = (uu___281_1665.unfold_attr);
            unfold_tac = (uu___281_1665.unfold_tac);
            pure_subterms_within_computations =
              (uu___281_1665.pure_subterms_within_computations);
            simplify = (uu___281_1665.simplify);
            erase_universes = (uu___281_1665.erase_universes);
            allow_unbound_universes = (uu___281_1665.allow_unbound_universes);
            reify_ = (uu___281_1665.reify_);
            compress_uvars = (uu___281_1665.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___281_1665.check_no_uvars);
            unmeta = (uu___281_1665.unmeta);
            unascribe = (uu___281_1665.unascribe);
            in_full_norm_request = (uu___281_1665.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___281_1665.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___282_1666 = fs  in
          {
            beta = (uu___282_1666.beta);
            iota = (uu___282_1666.iota);
            zeta = (uu___282_1666.zeta);
            weak = (uu___282_1666.weak);
            hnf = (uu___282_1666.hnf);
            primops = (uu___282_1666.primops);
            do_not_unfold_pure_lets = (uu___282_1666.do_not_unfold_pure_lets);
            unfold_until = (uu___282_1666.unfold_until);
            unfold_only = (uu___282_1666.unfold_only);
            unfold_fully = (uu___282_1666.unfold_fully);
            unfold_attr = (uu___282_1666.unfold_attr);
            unfold_tac = (uu___282_1666.unfold_tac);
            pure_subterms_within_computations =
              (uu___282_1666.pure_subterms_within_computations);
            simplify = (uu___282_1666.simplify);
            erase_universes = (uu___282_1666.erase_universes);
            allow_unbound_universes = (uu___282_1666.allow_unbound_universes);
            reify_ = (uu___282_1666.reify_);
            compress_uvars = (uu___282_1666.compress_uvars);
            no_full_norm = (uu___282_1666.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___282_1666.unmeta);
            unascribe = (uu___282_1666.unascribe);
            in_full_norm_request = (uu___282_1666.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___282_1666.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___283_1667 = fs  in
          {
            beta = (uu___283_1667.beta);
            iota = (uu___283_1667.iota);
            zeta = (uu___283_1667.zeta);
            weak = (uu___283_1667.weak);
            hnf = (uu___283_1667.hnf);
            primops = (uu___283_1667.primops);
            do_not_unfold_pure_lets = (uu___283_1667.do_not_unfold_pure_lets);
            unfold_until = (uu___283_1667.unfold_until);
            unfold_only = (uu___283_1667.unfold_only);
            unfold_fully = (uu___283_1667.unfold_fully);
            unfold_attr = (uu___283_1667.unfold_attr);
            unfold_tac = (uu___283_1667.unfold_tac);
            pure_subterms_within_computations =
              (uu___283_1667.pure_subterms_within_computations);
            simplify = (uu___283_1667.simplify);
            erase_universes = (uu___283_1667.erase_universes);
            allow_unbound_universes = (uu___283_1667.allow_unbound_universes);
            reify_ = (uu___283_1667.reify_);
            compress_uvars = (uu___283_1667.compress_uvars);
            no_full_norm = (uu___283_1667.no_full_norm);
            check_no_uvars = (uu___283_1667.check_no_uvars);
            unmeta = true;
            unascribe = (uu___283_1667.unascribe);
            in_full_norm_request = (uu___283_1667.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___283_1667.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___284_1668 = fs  in
          {
            beta = (uu___284_1668.beta);
            iota = (uu___284_1668.iota);
            zeta = (uu___284_1668.zeta);
            weak = (uu___284_1668.weak);
            hnf = (uu___284_1668.hnf);
            primops = (uu___284_1668.primops);
            do_not_unfold_pure_lets = (uu___284_1668.do_not_unfold_pure_lets);
            unfold_until = (uu___284_1668.unfold_until);
            unfold_only = (uu___284_1668.unfold_only);
            unfold_fully = (uu___284_1668.unfold_fully);
            unfold_attr = (uu___284_1668.unfold_attr);
            unfold_tac = (uu___284_1668.unfold_tac);
            pure_subterms_within_computations =
              (uu___284_1668.pure_subterms_within_computations);
            simplify = (uu___284_1668.simplify);
            erase_universes = (uu___284_1668.erase_universes);
            allow_unbound_universes = (uu___284_1668.allow_unbound_universes);
            reify_ = (uu___284_1668.reify_);
            compress_uvars = (uu___284_1668.compress_uvars);
            no_full_norm = (uu___284_1668.no_full_norm);
            check_no_uvars = (uu___284_1668.check_no_uvars);
            unmeta = (uu___284_1668.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___284_1668.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___284_1668.weakly_reduce_scrutinee)
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1721  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____2010 -> false
  
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
    match projectee with | Univ _0 -> true | uu____2114 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____2127 -> false
  
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
  top: Prims.bool ;
  cfg: Prims.bool ;
  primop: Prims.bool ;
  unfolding: Prims.bool ;
  b380: Prims.bool ;
  wpe: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__top : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__top
  
let (__proj__Mkdebug_switches__item__cfg : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__cfg
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__unfolding :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__unfolding
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__wpe : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__wpe
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; top = __fname__top; cfg = __fname__cfg;
        primop = __fname__primop; unfolding = __fname__unfolding;
        b380 = __fname__b380; wpe = __fname__wpe;
        norm_delayed = __fname__norm_delayed;
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
  
let (cfg_to_string : cfg -> Prims.string) =
  fun cfg  ->
    let uu____2508 =
      let uu____2511 =
        let uu____2514 =
          let uu____2515 = steps_to_string cfg.steps  in
          FStar_Util.format1 "  steps = %s" uu____2515  in
        [uu____2514; "}"]  in
      "{" :: uu____2511  in
    FStar_String.concat "\n" uu____2508
  
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____2547 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2547 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2561 = FStar_Util.psmap_empty ()  in add_steps uu____2561 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2576 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2576
  
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
    match projectee with | Arg _0 -> true | uu____2734 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2772 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2810 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2883 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2933 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2991 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____3035 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____3075 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____3113 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____3131 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3158 = FStar_Syntax_Util.head_and_args' t  in
    match uu____3158 with | (hd1,uu____3174) -> hd1
  
let mk :
  'Auu____3201 .
    'Auu____3201 ->
      FStar_Range.range -> 'Auu____3201 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3264 = FStar_ST.op_Bang r  in
          match uu____3264 with
          | FStar_Pervasives_Native.Some uu____3312 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3384 =
      FStar_List.map
        (fun uu____3398  ->
           match uu____3398 with
           | (bopt,c) ->
               let uu____3411 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3413 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3411 uu____3413) env
       in
    FStar_All.pipe_right uu____3384 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___242_3416  ->
    match uu___242_3416 with
    | Clos (env,t,uu____3419,uu____3420) ->
        let uu____3465 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3472 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3465 uu____3472
    | Univ uu____3473 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___243_3478  ->
    match uu___243_3478 with
    | Arg (c,uu____3480,uu____3481) ->
        let uu____3482 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3482
    | MemoLazy uu____3483 -> "MemoLazy"
    | Abs (uu____3490,bs,uu____3492,uu____3493,uu____3494) ->
        let uu____3499 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3499
    | UnivArgs uu____3506 -> "UnivArgs"
    | Match uu____3513 -> "Match"
    | App (uu____3522,t,uu____3524,uu____3525) ->
        let uu____3526 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3526
    | Meta (uu____3527,m,uu____3529) -> "Meta"
    | Let uu____3530 -> "Let"
    | Cfg uu____3539 -> "Cfg"
    | Debug (t,uu____3541) ->
        let uu____3542 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3542
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3552 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3552 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_top : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).top then f () else () 
let (log_cfg : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).cfg then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let (log_unfolding : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).unfolding then f () else () 
let is_empty : 'Auu____3641 . 'Auu____3641 Prims.list -> Prims.bool =
  fun uu___244_3648  ->
    match uu___244_3648 with | [] -> true | uu____3651 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3683 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3683
      with
      | uu____3702 ->
          let uu____3703 =
            let uu____3704 = FStar_Syntax_Print.db_to_string x  in
            let uu____3705 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3704
              uu____3705
             in
          failwith uu____3703
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3713 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3713
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3717 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3717
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3721 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3721
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
          let uu____3755 =
            FStar_List.fold_left
              (fun uu____3781  ->
                 fun u1  ->
                   match uu____3781 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3806 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3806 with
                        | (k_u,n1) ->
                            let uu____3821 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3821
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3755 with
          | (uu____3839,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3866 =
                   let uu____3867 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3867  in
                 match uu____3866 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3885 ->
                     let uu____3886 =
                       let uu____3887 = FStar_Util.string_of_int x  in
                       FStar_Util.format1
                         "Impossible: universe variable u@%s bound to a term"
                         uu____3887
                        in
                     failwith uu____3886
               with
               | uu____3895 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____3899 =
                        let uu____3900 = FStar_Util.string_of_int x  in
                        Prims.strcat "Universe variable not found: u@"
                          uu____3900
                         in
                      failwith uu____3899))
          | FStar_Syntax_Syntax.U_unif uu____3903 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3912 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3921 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3928 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3928 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3945 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3945 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3953 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3961 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3961 with
                                  | (uu____3966,m) -> n1 <= m))
                           in
                        if uu____3953 then rest1 else us1
                    | uu____3971 -> us1)
               | uu____3976 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3980 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____3980
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3984 = aux u  in
           match uu____3984 with
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
            (fun uu____4136  ->
               let uu____4137 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4138 = env_to_string env  in
               let uu____4139 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____4137 uu____4138 uu____4139);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____4148 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____4151 ->
                    let uu____4174 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____4174
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____4175 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____4176 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____4177 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____4178 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____4202 ->
                           let uu____4215 =
                             let uu____4216 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4217 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4216 uu____4217
                              in
                           failwith uu____4215
                       | uu____4220 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___245_4255  ->
                                         match uu___245_4255 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4262 =
                                               let uu____4269 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4269)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4262
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___289_4279 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___289_4279.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___289_4279.FStar_Syntax_Syntax.sort)
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
                                              | uu____4284 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4287 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___290_4291 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___290_4291.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___290_4291.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4312 =
                        let uu____4313 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4313  in
                      mk uu____4312 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4321 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4321  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4323 = lookup_bvar env x  in
                    (match uu____4323 with
                     | Univ uu____4326 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___291_4330 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___291_4330.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___291_4330.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4336,uu____4337) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4426  ->
                              fun stack1  ->
                                match uu____4426 with
                                | (a,aq) ->
                                    let uu____4438 =
                                      let uu____4439 =
                                        let uu____4446 =
                                          let uu____4447 =
                                            let uu____4478 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4478, false)  in
                                          Clos uu____4447  in
                                        (uu____4446, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4439  in
                                    uu____4438 :: stack1) args)
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
                    let uu____4666 = close_binders cfg env bs  in
                    (match uu____4666 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4721 =
                      let uu____4734 =
                        let uu____4743 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4743]  in
                      close_binders cfg env uu____4734  in
                    (match uu____4721 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4788 =
                             let uu____4789 =
                               let uu____4796 =
                                 let uu____4797 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4797
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4796, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4789  in
                           mk uu____4788 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4896 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4896
                      | FStar_Util.Inr c ->
                          let uu____4910 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4910
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4929 =
                        let uu____4930 =
                          let uu____4957 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4957, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4930  in
                      mk uu____4929 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____5003 =
                            let uu____5004 =
                              let uu____5011 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____5011, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____5004  in
                          mk uu____5003 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____5063  -> dummy :: env1) env
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
                    let uu____5084 =
                      let uu____5095 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____5095
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____5114 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___292_5130 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___292_5130.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___292_5130.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____5114))
                       in
                    (match uu____5084 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___293_5148 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___293_5148.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___293_5148.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___293_5148.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___293_5148.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____5162,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____5225  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____5242 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5242
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5254  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5278 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5278
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___294_5286 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___294_5286.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___294_5286.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___295_5287 = lb  in
                      let uu____5288 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___295_5287.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___295_5287.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5288;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___295_5287.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___295_5287.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5320  -> fun env1  -> dummy :: env1)
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
            (fun uu____5409  ->
               let uu____5410 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5411 = env_to_string env  in
               let uu____5412 = stack_to_string stack  in
               let uu____5413 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5410 uu____5411 uu____5412 uu____5413);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5418,uu____5419),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5498 = close_binders cfg env' bs  in
               (match uu____5498 with
                | (bs1,uu____5514) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5534 =
                      let uu___296_5537 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___296_5537.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___296_5537.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5534)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5593 =
                 match uu____5593 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5708 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5737 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5821  ->
                                     fun uu____5822  ->
                                       match (uu____5821, uu____5822) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5961 = norm_pat env4 p1
                                              in
                                           (match uu____5961 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5737 with
                            | (pats1,env4) ->
                                ((let uu___297_6123 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___297_6123.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___298_6142 = x  in
                             let uu____6143 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___298_6142.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___298_6142.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____6143
                             }  in
                           ((let uu___299_6157 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___299_6157.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___300_6168 = x  in
                             let uu____6169 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___300_6168.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___300_6168.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____6169
                             }  in
                           ((let uu___301_6183 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___301_6183.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___302_6199 = x  in
                             let uu____6200 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___302_6199.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___302_6199.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____6200
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___303_6217 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___303_6217.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____6222 = norm_pat env2 pat  in
                     (match uu____6222 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6291 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6291
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6310 =
                   let uu____6311 =
                     let uu____6334 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6334)  in
                   FStar_Syntax_Syntax.Tm_match uu____6311  in
                 mk uu____6310 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6449 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6558  ->
                                       match uu____6558 with
                                       | (a,q) ->
                                           let uu____6585 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6585, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6449
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6598 =
                       let uu____6605 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6605)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6598
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6617 =
                       let uu____6626 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6626)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6617
                 | uu____6631 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6637 -> failwith "Impossible: unexpected stack element")

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
        let uu____6653 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6736  ->
                  fun uu____6737  ->
                    match (uu____6736, uu____6737) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___304_6877 = b  in
                          let uu____6878 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___304_6877.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___304_6877.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6878
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6653 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____7015 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____7028 = inline_closure_env cfg env [] t  in
                 let uu____7029 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____7028 uu____7029
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____7042 = inline_closure_env cfg env [] t  in
                 let uu____7043 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____7042 uu____7043
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____7097  ->
                           match uu____7097 with
                           | (a,q) ->
                               let uu____7118 =
                                 inline_closure_env cfg env [] a  in
                               (uu____7118, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___246_7135  ->
                           match uu___246_7135 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____7139 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____7139
                           | f -> f))
                    in
                 let uu____7143 =
                   let uu___305_7144 = c1  in
                   let uu____7145 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____7145;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___305_7144.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____7143)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___247_7155  ->
            match uu___247_7155 with
            | FStar_Syntax_Syntax.DECREASES uu____7156 -> false
            | uu____7159 -> true))

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
                   (fun uu___248_7177  ->
                      match uu___248_7177 with
                      | FStar_Syntax_Syntax.DECREASES uu____7178 -> false
                      | uu____7181 -> true))
               in
            let rc1 =
              let uu___306_7183 = rc  in
              let uu____7184 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___306_7183.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____7184;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____7193 -> lopt

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
    let uu____7310 =
      let uu____7319 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____7319  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____7310  in
  let arg_as_bounded_int uu____7349 =
    match uu____7349 with
    | (a,uu____7363) ->
        let uu____7374 =
          let uu____7375 = FStar_Syntax_Subst.compress a  in
          uu____7375.FStar_Syntax_Syntax.n  in
        (match uu____7374 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____7385;
                FStar_Syntax_Syntax.vars = uu____7386;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____7388;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____7389;_},uu____7390)::[])
             when
             let uu____7439 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7439 "int_to_t" ->
             let uu____7440 =
               let uu____7445 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7445)  in
             FStar_Pervasives_Native.Some uu____7440
         | uu____7450 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7498 = f a  in FStar_Pervasives_Native.Some uu____7498
    | uu____7499 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7555 = f a0 a1  in FStar_Pervasives_Native.Some uu____7555
    | uu____7556 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7614 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7614  in
  let binary_op as_a f res args =
    let uu____7687 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7687  in
  let as_primitive_step is_strong uu____7726 =
    match uu____7726 with
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
           let uu____7786 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7786)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7822 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7822)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7851 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7851)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7887 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7887)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7923 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7923)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____8065 =
          let uu____8074 = as_a a  in
          let uu____8077 = as_b b  in (uu____8074, uu____8077)  in
        (match uu____8065 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____8092 =
               let uu____8093 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____8093  in
             FStar_Pervasives_Native.Some uu____8092
         | uu____8094 -> FStar_Pervasives_Native.None)
    | uu____8103 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____8123 =
        let uu____8124 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____8124  in
      mk uu____8123 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____8138 =
      let uu____8141 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____8141  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____8138  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____8183 =
      let uu____8184 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____8184  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____8183
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____8262 = arg_as_string a1  in
        (match uu____8262 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8268 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____8268 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8281 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____8281
              | uu____8282 -> FStar_Pervasives_Native.None)
         | uu____8287 -> FStar_Pervasives_Native.None)
    | uu____8290 -> FStar_Pervasives_Native.None  in
  let string_split' psc args =
    match args with
    | a1::a2::[] ->
        let uu____8364 = arg_as_list FStar_Syntax_Embeddings.e_char a1  in
        (match uu____8364 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8380 = arg_as_string a2  in
             (match uu____8380 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8389 =
                    let uu____8390 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string
                       in
                    FStar_Syntax_Embeddings.embed uu____8390 psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____8389
              | uu____8397 -> FStar_Pervasives_Native.None)
         | uu____8400 -> FStar_Pervasives_Native.None)
    | uu____8406 -> FStar_Pervasives_Native.None  in
  let string_substring' psc args =
    match args with
    | a1::a2::a3::[] ->
        let uu____8437 =
          let uu____8450 = arg_as_string a1  in
          let uu____8453 = arg_as_int a2  in
          let uu____8456 = arg_as_int a3  in
          (uu____8450, uu____8453, uu____8456)  in
        (match uu____8437 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____8487 =
                  FStar_Syntax_Embeddings.embed
                    FStar_Syntax_Embeddings.e_string psc.psc_range r
                   in
                FStar_Pervasives_Native.Some uu____8487
              with | uu____8493 -> FStar_Pervasives_Native.None)
         | uu____8494 -> FStar_Pervasives_Native.None)
    | uu____8507 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____8521 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____8521
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8558 =
          let uu____8579 = arg_as_string fn  in
          let uu____8582 = arg_as_int from_line  in
          let uu____8585 = arg_as_int from_col  in
          let uu____8588 = arg_as_int to_line  in
          let uu____8591 = arg_as_int to_col  in
          (uu____8579, uu____8582, uu____8585, uu____8588, uu____8591)  in
        (match uu____8558 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8622 =
                 let uu____8623 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8624 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8623 uu____8624  in
               let uu____8625 =
                 let uu____8626 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8627 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8626 uu____8627  in
               FStar_Range.mk_range fn1 uu____8622 uu____8625  in
             let uu____8628 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8628
         | uu____8629 -> FStar_Pervasives_Native.None)
    | uu____8650 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8683)::(a1,uu____8685)::(a2,uu____8687)::[] ->
        let uu____8744 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8744 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8749 -> FStar_Pervasives_Native.None)
    | uu____8750 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8785)::[] ->
        let uu____8802 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8802 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8808 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8808
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8809 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8837 =
      let uu____8854 =
        let uu____8871 =
          let uu____8888 =
            let uu____8905 =
              let uu____8922 =
                let uu____8939 =
                  let uu____8956 =
                    let uu____8973 =
                      let uu____8990 =
                        let uu____9007 =
                          let uu____9024 =
                            let uu____9041 =
                              let uu____9058 =
                                let uu____9075 =
                                  let uu____9092 =
                                    let uu____9109 =
                                      let uu____9126 =
                                        let uu____9143 =
                                          let uu____9160 =
                                            let uu____9177 =
                                              let uu____9194 =
                                                let uu____9209 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____9209,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____9218 =
                                                let uu____9235 =
                                                  let uu____9250 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____9250,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____9263 =
                                                  let uu____9280 =
                                                    let uu____9295 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____9295,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____9304 =
                                                    let uu____9321 =
                                                      let uu____9336 =
                                                        FStar_Parser_Const.p2l
                                                          ["FStar";
                                                          "String";
                                                          "split"]
                                                         in
                                                      (uu____9336,
                                                        (Prims.parse_int "2"),
                                                        string_split')
                                                       in
                                                    let uu____9345 =
                                                      let uu____9362 =
                                                        let uu____9377 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "String";
                                                            "substring"]
                                                           in
                                                        (uu____9377,
                                                          (Prims.parse_int "3"),
                                                          string_substring')
                                                         in
                                                      let uu____9386 =
                                                        let uu____9403 =
                                                          let uu____9418 =
                                                            FStar_Parser_Const.p2l
                                                              ["Prims";
                                                              "mk_range"]
                                                             in
                                                          (uu____9418,
                                                            (Prims.parse_int "5"),
                                                            mk_range1)
                                                           in
                                                        [uu____9403]  in
                                                      uu____9362 ::
                                                        uu____9386
                                                       in
                                                    uu____9321 :: uu____9345
                                                     in
                                                  uu____9280 :: uu____9304
                                                   in
                                                uu____9235 :: uu____9263  in
                                              uu____9194 :: uu____9218  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____9177
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____9160
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____9143
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____9126
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____9109
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____9666 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____9666 y)))
                                    :: uu____9092
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____9075
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____9058
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____9041
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____9024
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____9007
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8990
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9861 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9861)))
                      :: uu____8973
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9891 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9891)))
                    :: uu____8956
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9921 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9921)))
                  :: uu____8939
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9951 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9951)))
                :: uu____8922
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8905
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8888
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8871
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8854
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8837
     in
  let weak_ops =
    let uu____10106 =
      let uu____10121 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____10121, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____10106]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____10201 =
        let uu____10206 =
          let uu____10207 = FStar_Syntax_Syntax.as_arg c  in [uu____10207]
           in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____10206  in
      uu____10201 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____10287 =
                let uu____10302 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____10302, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____10324  ->
                          fun uu____10325  ->
                            match (uu____10324, uu____10325) with
                            | ((int_to_t1,x),(uu____10344,y)) ->
                                let uu____10354 =
                                  FStar_BigInt.add_big_int x y  in
                                int_as_bounded r int_to_t1 uu____10354)))
                 in
              let uu____10355 =
                let uu____10372 =
                  let uu____10387 =
                    FStar_Parser_Const.p2l ["FStar"; m; "sub"]  in
                  (uu____10387, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10409  ->
                            fun uu____10410  ->
                              match (uu____10409, uu____10410) with
                              | ((int_to_t1,x),(uu____10429,y)) ->
                                  let uu____10439 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10439)))
                   in
                let uu____10440 =
                  let uu____10457 =
                    let uu____10472 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____10472, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____10494  ->
                              fun uu____10495  ->
                                match (uu____10494, uu____10495) with
                                | ((int_to_t1,x),(uu____10514,y)) ->
                                    let uu____10524 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____10524)))
                     in
                  let uu____10525 =
                    let uu____10542 =
                      let uu____10557 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____10557, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____10575  ->
                                match uu____10575 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____10542]  in
                  uu____10457 :: uu____10525  in
                uu____10372 :: uu____10440  in
              uu____10287 :: uu____10355))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10705 =
                let uu____10720 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____10720, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____10742  ->
                          fun uu____10743  ->
                            match (uu____10742, uu____10743) with
                            | ((int_to_t1,x),(uu____10762,y)) ->
                                let uu____10772 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded r int_to_t1 uu____10772)))
                 in
              let uu____10773 =
                let uu____10790 =
                  let uu____10805 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10805, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10827  ->
                            fun uu____10828  ->
                              match (uu____10827, uu____10828) with
                              | ((int_to_t1,x),(uu____10847,y)) ->
                                  let uu____10857 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10857)))
                   in
                [uu____10790]  in
              uu____10705 :: uu____10773))
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
    | (_typ,uu____10987)::(a1,uu____10989)::(a2,uu____10991)::[] ->
        let uu____11048 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____11048 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___309_11052 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___309_11052.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___309_11052.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___310_11054 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___310_11054.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___310_11054.FStar_Syntax_Syntax.vars)
                })
         | uu____11055 -> FStar_Pervasives_Native.None)
    | (_typ,uu____11057)::uu____11058::(a1,uu____11060)::(a2,uu____11062)::[]
        ->
        let uu____11135 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____11135 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___309_11139 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___309_11139.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___309_11139.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___310_11141 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___310_11141.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___310_11141.FStar_Syntax_Syntax.vars)
                })
         | uu____11142 -> FStar_Pervasives_Native.None)
    | uu____11143 -> failwith "Unexpected number of arguments"  in
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
    let uu____11197 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____11197 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____11245 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11245) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____11307  ->
           fun subst1  ->
             match uu____11307 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____11348,uu____11349)) ->
                      let uu____11408 = b  in
                      (match uu____11408 with
                       | (bv,uu____11416) ->
                           let uu____11417 =
                             let uu____11418 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____11418  in
                           if uu____11417
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____11423 = unembed_binder term1  in
                              match uu____11423 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____11430 =
                                      let uu___311_11431 = bv  in
                                      let uu____11432 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___311_11431.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___311_11431.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____11432
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____11430
                                     in
                                  let b_for_x =
                                    let uu____11438 =
                                      let uu____11445 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____11445)
                                       in
                                    FStar_Syntax_Syntax.NT uu____11438  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___249_11461  ->
                                         match uu___249_11461 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____11462,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____11464;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____11465;_})
                                             ->
                                             let uu____11470 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____11470
                                         | uu____11471 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____11472 -> subst1)) env []
  
let reduce_primops :
  'Auu____11495 'Auu____11496 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11495) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11496 ->
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
            (let uu____11544 = FStar_Syntax_Util.head_and_args tm  in
             match uu____11544 with
             | (head1,args) ->
                 let uu____11589 =
                   let uu____11590 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11590.FStar_Syntax_Syntax.n  in
                 (match uu____11589 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____11596 = find_prim_step cfg fv  in
                      (match uu____11596 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____11624  ->
                                   let uu____11625 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____11626 =
                                     FStar_Util.string_of_int l  in
                                   let uu____11633 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____11625 uu____11626 uu____11633);
                              tm)
                           else
                             (let uu____11635 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____11635 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____11772  ->
                                        let uu____11773 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____11773);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____11776  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____11778 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____11778 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____11786  ->
                                              let uu____11787 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____11787);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____11793  ->
                                              let uu____11794 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____11795 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____11794 uu____11795);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____11796 ->
                           (log_primops cfg
                              (fun uu____11800  ->
                                 let uu____11801 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____11801);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11805  ->
                            let uu____11806 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11806);
                       (match args with
                        | (a1,uu____11810)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____11835 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11849  ->
                            let uu____11850 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11850);
                       (match args with
                        | (t,uu____11854)::(r,uu____11856)::[] ->
                            let uu____11897 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11897 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11903 -> tm))
                  | uu____11914 -> tm))
  
let reduce_equality :
  'Auu____11925 'Auu____11926 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11925) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11926 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___312_11972 = cfg  in
         {
           steps =
             (let uu___313_11975 = default_steps  in
              {
                beta = (uu___313_11975.beta);
                iota = (uu___313_11975.iota);
                zeta = (uu___313_11975.zeta);
                weak = (uu___313_11975.weak);
                hnf = (uu___313_11975.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___313_11975.do_not_unfold_pure_lets);
                unfold_until = (uu___313_11975.unfold_until);
                unfold_only = (uu___313_11975.unfold_only);
                unfold_fully = (uu___313_11975.unfold_fully);
                unfold_attr = (uu___313_11975.unfold_attr);
                unfold_tac = (uu___313_11975.unfold_tac);
                pure_subterms_within_computations =
                  (uu___313_11975.pure_subterms_within_computations);
                simplify = (uu___313_11975.simplify);
                erase_universes = (uu___313_11975.erase_universes);
                allow_unbound_universes =
                  (uu___313_11975.allow_unbound_universes);
                reify_ = (uu___313_11975.reify_);
                compress_uvars = (uu___313_11975.compress_uvars);
                no_full_norm = (uu___313_11975.no_full_norm);
                check_no_uvars = (uu___313_11975.check_no_uvars);
                unmeta = (uu___313_11975.unmeta);
                unascribe = (uu___313_11975.unascribe);
                in_full_norm_request = (uu___313_11975.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___313_11975.weakly_reduce_scrutinee)
              });
           tcenv = (uu___312_11972.tcenv);
           debug = (uu___312_11972.debug);
           delta_level = (uu___312_11972.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___312_11972.strong);
           memoize_lazy = (uu___312_11972.memoize_lazy);
           normalize_pure_lets = (uu___312_11972.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11982 .
    FStar_Syntax_Syntax.term -> 'Auu____11982 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11997 =
        let uu____12004 =
          let uu____12005 = FStar_Syntax_Util.un_uinst hd1  in
          uu____12005.FStar_Syntax_Syntax.n  in
        (uu____12004, args)  in
      match uu____11997 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12011::uu____12012::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12016::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____12021::uu____12022::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____12025 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___250_12038  ->
    match uu___250_12038 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.Reify  -> [Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____12044 =
          let uu____12047 =
            let uu____12048 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____12048  in
          [uu____12047]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____12044
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____12054 =
          let uu____12057 =
            let uu____12058 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____12058  in
          [uu____12057]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____12054
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____12081 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____12081)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____12132 =
            let uu____12137 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____12137 s  in
          match uu____12132 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____12153 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____12153
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____12179::(tm,uu____12181)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____12210)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____12231)::uu____12232::(tm,uu____12234)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____12275 =
              let uu____12280 = full_norm steps  in parse_steps uu____12280
               in
            (match uu____12275 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____12319 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___251_12338  ->
    match uu___251_12338 with
    | (App
        (uu____12341,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12342;
                       FStar_Syntax_Syntax.vars = uu____12343;_},uu____12344,uu____12345))::uu____12346
        -> true
    | uu____12351 -> false
  
let firstn :
  'Auu____12360 .
    Prims.int ->
      'Auu____12360 Prims.list ->
        ('Auu____12360 Prims.list,'Auu____12360 Prims.list)
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
          (uu____12402,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12403;
                         FStar_Syntax_Syntax.vars = uu____12404;_},uu____12405,uu____12406))::uu____12407
          -> (cfg.steps).reify_
      | uu____12412 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____12435) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____12445) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____12466  ->
                  match uu____12466 with
                  | (a,uu____12476) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____12486 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____12509 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____12510 -> false
    | FStar_Syntax_Syntax.Tm_type uu____12523 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____12524 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____12525 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____12526 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____12527 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____12528 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____12535 -> false
    | FStar_Syntax_Syntax.Tm_let uu____12542 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____12555 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____12574 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____12589 -> true
    | FStar_Syntax_Syntax.Tm_match uu____12596 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____12666  ->
                   match uu____12666 with
                   | (a,uu____12676) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12687) ->
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
                     (fun uu____12815  ->
                        match uu____12815 with
                        | (a,uu____12825) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____12834,uu____12835,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____12841,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____12847 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____12854 -> false
            | FStar_Syntax_Syntax.Meta_named uu____12855 -> false))
  
let decide_unfolding :
  'Auu____12870 .
    cfg ->
      'Auu____12870 Prims.list ->
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
                (fun uu____12962  ->
                   let uu____12963 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____12964 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____12965 =
                     let uu____12966 =
                       let uu____12969 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____12969
                        in
                     stack_to_string uu____12966  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____12963 uu____12964 uu____12965);
              (let attrs =
                 let uu____12995 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____12995 with
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
                   (fun uu____13123  ->
                      fun uu____13124  ->
                        match (uu____13123, uu____13124) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____13184 =
                 match uu____13184 with
                 | (x,y,z) ->
                     let uu____13194 = FStar_Util.string_of_bool x  in
                     let uu____13195 = FStar_Util.string_of_bool y  in
                     let uu____13196 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____13194 uu____13195
                       uu____13196
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____13242 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____13288  ->
                           let uu____13289 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____13290 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____13289 uu____13290);
                      if b then reif else no)
                 | uu____13298 when
                     let uu____13339 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____13339 ->
                     (log_unfolding cfg
                        (fun uu____13344  ->
                           FStar_Util.print_string
                             " >> It's a primop, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____13346),uu____13347);
                        FStar_Syntax_Syntax.sigrng = uu____13348;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____13350;
                        FStar_Syntax_Syntax.sigattrs = uu____13351;_},uu____13352),uu____13353),uu____13354,uu____13355,uu____13356)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (log_unfolding cfg
                        (fun uu____13461  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____13462,uu____13463,uu____13464,uu____13465) when
                     (cfg.steps).unfold_tac &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (log_unfolding cfg
                        (fun uu____13532  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____13534),uu____13535);
                        FStar_Syntax_Syntax.sigrng = uu____13536;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____13538;
                        FStar_Syntax_Syntax.sigattrs = uu____13539;_},uu____13540),uu____13541),uu____13542,uu____13543,uu____13544)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     (log_unfolding cfg
                        (fun uu____13649  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____13650,FStar_Pervasives_Native.Some
                    uu____13651,uu____13652,uu____13653) ->
                     (log_unfolding cfg
                        (fun uu____13721  ->
                           let uu____13722 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13722);
                      (let uu____13723 =
                         let uu____13732 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13752 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13752
                            in
                         let uu____13759 =
                           let uu____13768 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13788 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13788
                              in
                           let uu____13797 =
                             let uu____13806 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13826 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13826
                                in
                             [uu____13806]  in
                           uu____13768 :: uu____13797  in
                         uu____13732 :: uu____13759  in
                       comb_or uu____13723))
                 | (uu____13857,uu____13858,FStar_Pervasives_Native.Some
                    uu____13859,uu____13860) ->
                     (log_unfolding cfg
                        (fun uu____13928  ->
                           let uu____13929 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13929);
                      (let uu____13930 =
                         let uu____13939 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13959 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13959
                            in
                         let uu____13966 =
                           let uu____13975 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13995 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13995
                              in
                           let uu____14004 =
                             let uu____14013 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____14033 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____14033
                                in
                             [uu____14013]  in
                           uu____13975 :: uu____14004  in
                         uu____13939 :: uu____13966  in
                       comb_or uu____13930))
                 | (uu____14064,uu____14065,uu____14066,FStar_Pervasives_Native.Some
                    uu____14067) ->
                     (log_unfolding cfg
                        (fun uu____14135  ->
                           let uu____14136 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____14136);
                      (let uu____14137 =
                         let uu____14146 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____14166 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____14166
                            in
                         let uu____14173 =
                           let uu____14182 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____14202 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____14202
                              in
                           let uu____14211 =
                             let uu____14220 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____14240 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____14240
                                in
                             [uu____14220]  in
                           uu____14182 :: uu____14211  in
                         uu____14146 :: uu____14173  in
                       comb_or uu____14137))
                 | uu____14271 ->
                     (log_unfolding cfg
                        (fun uu____14317  ->
                           let uu____14318 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____14319 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____14320 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____14318 uu____14319 uu____14320);
                      (let uu____14321 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___252_14325  ->
                                 match uu___252_14325 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____14321))
                  in
               log_unfolding cfg
                 (fun uu____14338  ->
                    let uu____14339 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____14340 = FStar_Range.string_of_range rng  in
                    let uu____14341 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____14339 uu____14340 uu____14341);
               (match res with
                | (false ,uu____14350,uu____14351) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___314_14367 = cfg  in
                      {
                        steps =
                          (let uu___315_14370 = cfg.steps  in
                           {
                             beta = (uu___315_14370.beta);
                             iota = (uu___315_14370.iota);
                             zeta = (uu___315_14370.zeta);
                             weak = (uu___315_14370.weak);
                             hnf = (uu___315_14370.hnf);
                             primops = (uu___315_14370.primops);
                             do_not_unfold_pure_lets =
                               (uu___315_14370.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___315_14370.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___315_14370.pure_subterms_within_computations);
                             simplify = (uu___315_14370.simplify);
                             erase_universes =
                               (uu___315_14370.erase_universes);
                             allow_unbound_universes =
                               (uu___315_14370.allow_unbound_universes);
                             reify_ = (uu___315_14370.reify_);
                             compress_uvars = (uu___315_14370.compress_uvars);
                             no_full_norm = (uu___315_14370.no_full_norm);
                             check_no_uvars = (uu___315_14370.check_no_uvars);
                             unmeta = (uu___315_14370.unmeta);
                             unascribe = (uu___315_14370.unascribe);
                             in_full_norm_request =
                               (uu___315_14370.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___315_14370.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___314_14367.tcenv);
                        debug = (uu___314_14367.debug);
                        delta_level = (uu___314_14367.delta_level);
                        primitive_steps = (uu___314_14367.primitive_steps);
                        strong = (uu___314_14367.strong);
                        memoize_lazy = (uu___314_14367.memoize_lazy);
                        normalize_pure_lets =
                          (uu___314_14367.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____14388 =
                      let uu____14395 = FStar_List.tl stack  in
                      (cfg, uu____14395)  in
                    FStar_Pervasives_Native.Some uu____14388
                | uu____14406 ->
                    let uu____14413 =
                      let uu____14414 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____14414
                       in
                    FStar_All.pipe_left failwith uu____14413))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____14730 ->
                   let uu____14753 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____14753
               | uu____14754 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____14762  ->
               let uu____14763 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____14764 = FStar_Syntax_Print.term_to_string t1  in
               let uu____14765 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____14772 =
                 let uu____14773 =
                   let uu____14776 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____14776
                    in
                 stack_to_string uu____14773  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____14763 uu____14764 uu____14765 uu____14772);
          log_cfg cfg
            (fun uu____14802  ->
               let uu____14803 = cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____14803);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____14807  ->
                     let uu____14808 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14808);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____14809 ->
               (log_unfolding cfg
                  (fun uu____14813  ->
                     let uu____14814 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14814);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____14815 ->
               (log_unfolding cfg
                  (fun uu____14819  ->
                     let uu____14820 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14820);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____14821 ->
               (log_unfolding cfg
                  (fun uu____14825  ->
                     let uu____14826 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14826);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14827;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____14828;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____14834  ->
                     let uu____14835 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14835);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14836;
                 FStar_Syntax_Syntax.fv_delta = uu____14837;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____14841  ->
                     let uu____14842 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14842);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14843;
                 FStar_Syntax_Syntax.fv_delta = uu____14844;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____14845);_}
               ->
               (log_unfolding cfg
                  (fun uu____14855  ->
                     let uu____14856 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14856);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14859 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14859  in
               let uu____14860 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14860 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____14893 ->
               let uu____14900 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14900
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____14936 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____14936)
               ->
               let cfg' =
                 let uu___316_14938 = cfg  in
                 {
                   steps =
                     (let uu___317_14941 = cfg.steps  in
                      {
                        beta = (uu___317_14941.beta);
                        iota = (uu___317_14941.iota);
                        zeta = (uu___317_14941.zeta);
                        weak = (uu___317_14941.weak);
                        hnf = (uu___317_14941.hnf);
                        primops = (uu___317_14941.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___317_14941.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___317_14941.unfold_attr);
                        unfold_tac = (uu___317_14941.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___317_14941.pure_subterms_within_computations);
                        simplify = (uu___317_14941.simplify);
                        erase_universes = (uu___317_14941.erase_universes);
                        allow_unbound_universes =
                          (uu___317_14941.allow_unbound_universes);
                        reify_ = (uu___317_14941.reify_);
                        compress_uvars = (uu___317_14941.compress_uvars);
                        no_full_norm = (uu___317_14941.no_full_norm);
                        check_no_uvars = (uu___317_14941.check_no_uvars);
                        unmeta = (uu___317_14941.unmeta);
                        unascribe = (uu___317_14941.unascribe);
                        in_full_norm_request =
                          (uu___317_14941.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___317_14941.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___316_14938.tcenv);
                   debug = (uu___316_14938.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___316_14938.primitive_steps);
                   strong = (uu___316_14938.strong);
                   memoize_lazy = (uu___316_14938.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____14946 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____14946 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14977  ->
                              fun stack1  ->
                                match uu____14977 with
                                | (a,aq) ->
                                    let uu____14989 =
                                      let uu____14990 =
                                        let uu____14997 =
                                          let uu____14998 =
                                            let uu____15029 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____15029, false)  in
                                          Clos uu____14998  in
                                        (uu____14997, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14990  in
                                    uu____14989 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____15117  ->
                          let uu____15118 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____15118);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____15142 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___253_15147  ->
                                match uu___253_15147 with
                                | UnfoldUntil uu____15148 -> true
                                | UnfoldOnly uu____15149 -> true
                                | UnfoldFully uu____15152 -> true
                                | uu____15155 -> false))
                         in
                      if uu____15142
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___318_15160 = cfg  in
                      let uu____15161 =
                        let uu___319_15162 = to_fsteps s  in
                        {
                          beta = (uu___319_15162.beta);
                          iota = (uu___319_15162.iota);
                          zeta = (uu___319_15162.zeta);
                          weak = (uu___319_15162.weak);
                          hnf = (uu___319_15162.hnf);
                          primops = (uu___319_15162.primops);
                          do_not_unfold_pure_lets =
                            (uu___319_15162.do_not_unfold_pure_lets);
                          unfold_until = (uu___319_15162.unfold_until);
                          unfold_only = (uu___319_15162.unfold_only);
                          unfold_fully = (uu___319_15162.unfold_fully);
                          unfold_attr = (uu___319_15162.unfold_attr);
                          unfold_tac = (uu___319_15162.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___319_15162.pure_subterms_within_computations);
                          simplify = (uu___319_15162.simplify);
                          erase_universes = (uu___319_15162.erase_universes);
                          allow_unbound_universes =
                            (uu___319_15162.allow_unbound_universes);
                          reify_ = (uu___319_15162.reify_);
                          compress_uvars = (uu___319_15162.compress_uvars);
                          no_full_norm = (uu___319_15162.no_full_norm);
                          check_no_uvars = (uu___319_15162.check_no_uvars);
                          unmeta = (uu___319_15162.unmeta);
                          unascribe = (uu___319_15162.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___319_15162.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____15161;
                        tcenv = (uu___318_15160.tcenv);
                        debug = (uu___318_15160.debug);
                        delta_level;
                        primitive_steps = (uu___318_15160.primitive_steps);
                        strong = (uu___318_15160.strong);
                        memoize_lazy = (uu___318_15160.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____15167 =
                          let uu____15168 =
                            let uu____15173 = FStar_Util.now ()  in
                            (t1, uu____15173)  in
                          Debug uu____15168  in
                        uu____15167 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____15177 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____15177
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____15186 =
                      let uu____15193 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____15193, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____15186  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____15202 = lookup_bvar env x  in
               (match uu____15202 with
                | Univ uu____15203 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____15252 = FStar_ST.op_Bang r  in
                      (match uu____15252 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____15370  ->
                                 let uu____15371 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____15372 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____15371
                                   uu____15372);
                            (let uu____15373 = maybe_weakly_reduced t'  in
                             if uu____15373
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____15374 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____15449)::uu____15450 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____15460,uu____15461))::stack_rest ->
                    (match c with
                     | Univ uu____15465 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____15474 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____15503  ->
                                    let uu____15504 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____15504);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____15538  ->
                                    let uu____15539 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____15539);
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
                       (fun uu____15607  ->
                          let uu____15608 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____15608);
                     norm cfg env stack1 t1)
                | (Match uu____15609)::uu____15610 ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____15623 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15623 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15659  -> dummy :: env1) env)
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
                                          let uu____15702 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15702)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15709 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15709.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15709.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15710 -> lopt  in
                           (log cfg
                              (fun uu____15716  ->
                                 let uu____15717 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15717);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15728 = cfg  in
                               {
                                 steps = (uu___321_15728.steps);
                                 tcenv = (uu___321_15728.tcenv);
                                 debug = (uu___321_15728.debug);
                                 delta_level = (uu___321_15728.delta_level);
                                 primitive_steps =
                                   (uu___321_15728.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15728.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15728.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____15731)::uu____15732 ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____15741 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15741 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15777  -> dummy :: env1) env)
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
                                          let uu____15820 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15820)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15827 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15827.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15827.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15828 -> lopt  in
                           (log cfg
                              (fun uu____15834  ->
                                 let uu____15835 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15835);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15846 = cfg  in
                               {
                                 steps = (uu___321_15846.steps);
                                 tcenv = (uu___321_15846.tcenv);
                                 debug = (uu___321_15846.debug);
                                 delta_level = (uu___321_15846.delta_level);
                                 primitive_steps =
                                   (uu___321_15846.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15846.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15846.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____15849)::uu____15850 ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____15861 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15861 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15897  -> dummy :: env1) env)
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
                                          let uu____15940 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15940)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15947 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15947.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15947.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15948 -> lopt  in
                           (log cfg
                              (fun uu____15954  ->
                                 let uu____15955 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15955);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15966 = cfg  in
                               {
                                 steps = (uu___321_15966.steps);
                                 tcenv = (uu___321_15966.tcenv);
                                 debug = (uu___321_15966.debug);
                                 delta_level = (uu___321_15966.delta_level);
                                 primitive_steps =
                                   (uu___321_15966.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15966.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15966.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____15969)::uu____15970 ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____15983 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15983 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16019  -> dummy :: env1) env)
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
                                          let uu____16062 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16062)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_16069 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_16069.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_16069.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16070 -> lopt  in
                           (log cfg
                              (fun uu____16076  ->
                                 let uu____16077 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16077);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_16088 = cfg  in
                               {
                                 steps = (uu___321_16088.steps);
                                 tcenv = (uu___321_16088.tcenv);
                                 debug = (uu___321_16088.debug);
                                 delta_level = (uu___321_16088.delta_level);
                                 primitive_steps =
                                   (uu___321_16088.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_16088.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_16088.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____16091)::uu____16092 ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____16105 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16105 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16141  -> dummy :: env1) env)
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
                                          let uu____16184 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16184)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_16191 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_16191.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_16191.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16192 -> lopt  in
                           (log cfg
                              (fun uu____16198  ->
                                 let uu____16199 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16199);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_16210 = cfg  in
                               {
                                 steps = (uu___321_16210.steps);
                                 tcenv = (uu___321_16210.tcenv);
                                 debug = (uu___321_16210.debug);
                                 delta_level = (uu___321_16210.delta_level);
                                 primitive_steps =
                                   (uu___321_16210.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_16210.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_16210.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____16213)::uu____16214 ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____16231 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16231 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16267  -> dummy :: env1) env)
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
                                          let uu____16310 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16310)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_16317 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_16317.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_16317.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16318 -> lopt  in
                           (log cfg
                              (fun uu____16324  ->
                                 let uu____16325 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16325);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_16336 = cfg  in
                               {
                                 steps = (uu___321_16336.steps);
                                 tcenv = (uu___321_16336.tcenv);
                                 debug = (uu___321_16336.debug);
                                 delta_level = (uu___321_16336.delta_level);
                                 primitive_steps =
                                   (uu___321_16336.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_16336.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_16336.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____16341 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____16341 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16377  -> dummy :: env1) env)
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
                                          let uu____16420 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____16420)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_16427 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_16427.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_16427.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____16428 -> lopt  in
                           (log cfg
                              (fun uu____16434  ->
                                 let uu____16435 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____16435);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_16446 = cfg  in
                               {
                                 steps = (uu___321_16446.steps);
                                 tcenv = (uu___321_16446.tcenv);
                                 debug = (uu___321_16446.debug);
                                 delta_level = (uu___321_16446.delta_level);
                                 primitive_steps =
                                   (uu___321_16446.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_16446.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_16446.normalize_pure_lets)
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
                      (fun uu____16489  ->
                         fun stack1  ->
                           match uu____16489 with
                           | (a,aq) ->
                               let uu____16501 =
                                 let uu____16502 =
                                   let uu____16509 =
                                     let uu____16510 =
                                       let uu____16541 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____16541, false)  in
                                     Clos uu____16510  in
                                   (uu____16509, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____16502  in
                               uu____16501 :: stack1) args)
                  in
               (log cfg
                  (fun uu____16629  ->
                     let uu____16630 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____16630);
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
                             ((let uu___322_16678 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___322_16678.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___322_16678.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____16679 ->
                      let uu____16694 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____16694)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____16697 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____16697 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____16728 =
                          let uu____16729 =
                            let uu____16736 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___323_16742 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___323_16742.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___323_16742.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____16736)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____16729  in
                        mk uu____16728 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____16765 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____16765
               else
                 (let uu____16767 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____16767 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____16775 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____16801  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____16775 c1  in
                      let t2 =
                        let uu____16825 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____16825 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____16938)::uu____16939 ->
                    (log cfg
                       (fun uu____16952  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____16953)::uu____16954 ->
                    (log cfg
                       (fun uu____16965  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____16966,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____16967;
                                   FStar_Syntax_Syntax.vars = uu____16968;_},uu____16969,uu____16970))::uu____16971
                    ->
                    (log cfg
                       (fun uu____16978  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____16979)::uu____16980 ->
                    (log cfg
                       (fun uu____16991  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____16992 ->
                    (log cfg
                       (fun uu____16995  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____16999  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____17024 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____17024
                         | FStar_Util.Inr c ->
                             let uu____17038 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____17038
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____17061 =
                               let uu____17062 =
                                 let uu____17089 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____17089, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____17062
                                in
                             mk uu____17061 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____17124 ->
                           let uu____17125 =
                             let uu____17126 =
                               let uu____17127 =
                                 let uu____17154 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____17154, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____17127
                                in
                             mk uu____17126 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____17125))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___324_17231 = cfg  in
                   {
                     steps =
                       (let uu___325_17234 = cfg.steps  in
                        {
                          beta = (uu___325_17234.beta);
                          iota = (uu___325_17234.iota);
                          zeta = (uu___325_17234.zeta);
                          weak = true;
                          hnf = (uu___325_17234.hnf);
                          primops = (uu___325_17234.primops);
                          do_not_unfold_pure_lets =
                            (uu___325_17234.do_not_unfold_pure_lets);
                          unfold_until = (uu___325_17234.unfold_until);
                          unfold_only = (uu___325_17234.unfold_only);
                          unfold_fully = (uu___325_17234.unfold_fully);
                          unfold_attr = (uu___325_17234.unfold_attr);
                          unfold_tac = (uu___325_17234.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___325_17234.pure_subterms_within_computations);
                          simplify = (uu___325_17234.simplify);
                          erase_universes = (uu___325_17234.erase_universes);
                          allow_unbound_universes =
                            (uu___325_17234.allow_unbound_universes);
                          reify_ = (uu___325_17234.reify_);
                          compress_uvars = (uu___325_17234.compress_uvars);
                          no_full_norm = (uu___325_17234.no_full_norm);
                          check_no_uvars = (uu___325_17234.check_no_uvars);
                          unmeta = (uu___325_17234.unmeta);
                          unascribe = (uu___325_17234.unascribe);
                          in_full_norm_request =
                            (uu___325_17234.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___325_17234.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___324_17231.tcenv);
                     debug = (uu___324_17231.debug);
                     delta_level = (uu___324_17231.delta_level);
                     primitive_steps = (uu___324_17231.primitive_steps);
                     strong = (uu___324_17231.strong);
                     memoize_lazy = (uu___324_17231.memoize_lazy);
                     normalize_pure_lets =
                       (uu___324_17231.normalize_pure_lets)
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
                         let uu____17270 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____17270 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___326_17290 = cfg  in
                               let uu____17291 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___326_17290.steps);
                                 tcenv = uu____17291;
                                 debug = (uu___326_17290.debug);
                                 delta_level = (uu___326_17290.delta_level);
                                 primitive_steps =
                                   (uu___326_17290.primitive_steps);
                                 strong = (uu___326_17290.strong);
                                 memoize_lazy = (uu___326_17290.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_17290.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____17298 =
                                 let uu____17299 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____17299  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____17298
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___327_17302 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___327_17302.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___327_17302.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___327_17302.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___327_17302.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____17303 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____17303
           | FStar_Syntax_Syntax.Tm_let
               ((uu____17314,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____17315;
                               FStar_Syntax_Syntax.lbunivs = uu____17316;
                               FStar_Syntax_Syntax.lbtyp = uu____17317;
                               FStar_Syntax_Syntax.lbeff = uu____17318;
                               FStar_Syntax_Syntax.lbdef = uu____17319;
                               FStar_Syntax_Syntax.lbattrs = uu____17320;
                               FStar_Syntax_Syntax.lbpos = uu____17321;_}::uu____17322),uu____17323)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____17363 =
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
               if uu____17363
               then
                 let binder =
                   let uu____17365 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____17365  in
                 let env1 =
                   let uu____17375 =
                     let uu____17382 =
                       let uu____17383 =
                         let uu____17414 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____17414,
                           false)
                          in
                       Clos uu____17383  in
                     ((FStar_Pervasives_Native.Some binder), uu____17382)  in
                   uu____17375 :: env  in
                 (log cfg
                    (fun uu____17509  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____17513  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____17514 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____17514))
                 else
                   (let uu____17516 =
                      let uu____17521 =
                        let uu____17522 =
                          let uu____17529 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____17529
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____17522]  in
                      FStar_Syntax_Subst.open_term uu____17521 body  in
                    match uu____17516 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____17556  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____17564 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____17564  in
                            FStar_Util.Inl
                              (let uu___328_17580 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___328_17580.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___328_17580.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____17583  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___329_17585 = lb  in
                             let uu____17586 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___329_17585.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___329_17585.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17586;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___329_17585.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___329_17585.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____17615  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___330_17640 = cfg  in
                             {
                               steps = (uu___330_17640.steps);
                               tcenv = (uu___330_17640.tcenv);
                               debug = (uu___330_17640.debug);
                               delta_level = (uu___330_17640.delta_level);
                               primitive_steps =
                                 (uu___330_17640.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___330_17640.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___330_17640.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____17643  ->
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
               let uu____17660 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____17660 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____17696 =
                               let uu___331_17697 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___331_17697.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___331_17697.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____17696  in
                           let uu____17698 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____17698 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____17724 =
                                   FStar_List.map (fun uu____17740  -> dummy)
                                     lbs1
                                    in
                                 let uu____17741 =
                                   let uu____17750 =
                                     FStar_List.map
                                       (fun uu____17772  -> dummy) xs1
                                      in
                                   FStar_List.append uu____17750 env  in
                                 FStar_List.append uu____17724 uu____17741
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____17798 =
                                       let uu___332_17799 = rc  in
                                       let uu____17800 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___332_17799.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____17800;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___332_17799.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____17798
                                 | uu____17809 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___333_17815 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___333_17815.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___333_17815.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___333_17815.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___333_17815.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____17825 =
                        FStar_List.map (fun uu____17841  -> dummy) lbs2  in
                      FStar_List.append uu____17825 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____17849 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____17849 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___334_17865 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___334_17865.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___334_17865.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____17894 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____17894
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____17913 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____17989  ->
                        match uu____17989 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___335_18110 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___335_18110.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___335_18110.FStar_Syntax_Syntax.sort)
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
               (match uu____17913 with
                | (rec_env,memos,uu____18337) ->
                    let uu____18390 =
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
                             let uu____18701 =
                               let uu____18708 =
                                 let uu____18709 =
                                   let uu____18740 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____18740, false)
                                    in
                                 Clos uu____18709  in
                               (FStar_Pervasives_Native.None, uu____18708)
                                in
                             uu____18701 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____18844  ->
                     let uu____18845 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____18845);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____18867 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____18869::uu____18870 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____18875) ->
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
                             | uu____18902 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____18918 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____18918
                              | uu____18931 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____18937 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____18961 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____18975 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____18988 =
                        let uu____18989 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____18990 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____18989 uu____18990
                         in
                      failwith uu____18988
                    else
                      (let uu____18992 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____18992)
                | uu____18993 -> norm cfg env stack t2))

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
              let uu____19002 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____19002 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____19016  ->
                        let uu____19017 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____19017);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____19028  ->
                        let uu____19029 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____19030 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____19029 uu____19030);
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
                      | (UnivArgs (us',uu____19043))::stack1 ->
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
                      | uu____19082 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____19085 ->
                          let uu____19088 =
                            let uu____19089 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____19089
                             in
                          failwith uu____19088
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
                  let uu___336_19113 = cfg  in
                  let uu____19114 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____19114;
                    tcenv = (uu___336_19113.tcenv);
                    debug = (uu___336_19113.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___336_19113.primitive_steps);
                    strong = (uu___336_19113.strong);
                    memoize_lazy = (uu___336_19113.memoize_lazy);
                    normalize_pure_lets =
                      (uu___336_19113.normalize_pure_lets)
                  }
                else cfg  in
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
                  (fun uu____19149  ->
                     let uu____19150 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____19151 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____19150
                       uu____19151);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____19153 =
                   let uu____19154 = FStar_Syntax_Subst.compress head3  in
                   uu____19154.FStar_Syntax_Syntax.n  in
                 match uu____19153 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____19172 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____19172
                        in
                     let uu____19173 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____19173 with
                      | (uu____19174,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____19184 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____19194 =
                                   let uu____19195 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____19195.FStar_Syntax_Syntax.n  in
                                 match uu____19194 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____19201,uu____19202))
                                     ->
                                     let uu____19211 =
                                       let uu____19212 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____19212.FStar_Syntax_Syntax.n  in
                                     (match uu____19211 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____19218,msrc,uu____19220))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____19229 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____19229
                                      | uu____19230 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____19231 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____19232 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____19232 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___337_19237 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___337_19237.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___337_19237.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___337_19237.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___337_19237.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___337_19237.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____19238 = FStar_List.tl stack  in
                                    let uu____19239 =
                                      let uu____19240 =
                                        let uu____19247 =
                                          let uu____19248 =
                                            let uu____19261 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____19261)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____19248
                                           in
                                        FStar_Syntax_Syntax.mk uu____19247
                                         in
                                      uu____19240
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____19238 uu____19239
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19277 =
                                      let uu____19278 = is_return body  in
                                      match uu____19278 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____19282;
                                            FStar_Syntax_Syntax.vars =
                                              uu____19283;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____19286 -> false  in
                                    if uu____19277
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
                                         let uu____19307 =
                                           let uu____19314 =
                                             let uu____19315 =
                                               let uu____19334 =
                                                 let uu____19343 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____19343]  in
                                               (uu____19334, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____19315
                                              in
                                           FStar_Syntax_Syntax.mk uu____19314
                                            in
                                         uu____19307
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____19385 =
                                           let uu____19386 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____19386.FStar_Syntax_Syntax.n
                                            in
                                         match uu____19385 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____19392::uu____19393::[])
                                             ->
                                             let uu____19398 =
                                               let uu____19405 =
                                                 let uu____19406 =
                                                   let uu____19413 =
                                                     let uu____19414 =
                                                       let uu____19415 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____19415
                                                        in
                                                     let uu____19416 =
                                                       let uu____19419 =
                                                         let uu____19420 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____19420
                                                          in
                                                       [uu____19419]  in
                                                     uu____19414 ::
                                                       uu____19416
                                                      in
                                                   (bind1, uu____19413)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____19406
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____19405
                                                in
                                             uu____19398
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____19426 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____19440 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____19440
                                         then
                                           let uu____19451 =
                                             let uu____19460 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____19460
                                              in
                                           let uu____19461 =
                                             let uu____19472 =
                                               let uu____19481 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____19481
                                                in
                                             [uu____19472]  in
                                           uu____19451 :: uu____19461
                                         else []  in
                                       let reified =
                                         let uu____19518 =
                                           let uu____19525 =
                                             let uu____19526 =
                                               let uu____19543 =
                                                 let uu____19554 =
                                                   let uu____19565 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____19574 =
                                                     let uu____19585 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____19585]  in
                                                   uu____19565 :: uu____19574
                                                    in
                                                 let uu____19618 =
                                                   let uu____19629 =
                                                     let uu____19640 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____19649 =
                                                       let uu____19660 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____19669 =
                                                         let uu____19680 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____19689 =
                                                           let uu____19700 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____19700]  in
                                                         uu____19680 ::
                                                           uu____19689
                                                          in
                                                       uu____19660 ::
                                                         uu____19669
                                                        in
                                                     uu____19640 ::
                                                       uu____19649
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____19629
                                                    in
                                                 FStar_List.append
                                                   uu____19554 uu____19618
                                                  in
                                               (bind_inst, uu____19543)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____19526
                                              in
                                           FStar_Syntax_Syntax.mk uu____19525
                                            in
                                         uu____19518
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____19784  ->
                                            let uu____19785 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____19786 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____19785 uu____19786);
                                       (let uu____19787 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____19787 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let maybe_unfold_action head4 =
                       let maybe_extract_fv t1 =
                         let t2 =
                           let uu____19841 =
                             let uu____19842 = FStar_Syntax_Subst.compress t1
                                in
                             uu____19842.FStar_Syntax_Syntax.n  in
                           match uu____19841 with
                           | FStar_Syntax_Syntax.Tm_uinst (t2,uu____19846) ->
                               t2
                           | uu____19851 -> head4  in
                         let uu____19852 =
                           let uu____19853 = FStar_Syntax_Subst.compress t2
                              in
                           uu____19853.FStar_Syntax_Syntax.n  in
                         match uu____19852 with
                         | FStar_Syntax_Syntax.Tm_fvar x ->
                             FStar_Pervasives_Native.Some x
                         | uu____19859 -> FStar_Pervasives_Native.None  in
                       let uu____19860 = maybe_extract_fv head4  in
                       match uu____19860 with
                       | FStar_Pervasives_Native.Some x when
                           let uu____19870 = FStar_Syntax_Syntax.lid_of_fv x
                              in
                           FStar_TypeChecker_Env.is_action cfg.tcenv
                             uu____19870
                           ->
                           let head5 = norm cfg env [] head4  in
                           let action_unfolded =
                             let uu____19875 = maybe_extract_fv head5  in
                             match uu____19875 with
                             | FStar_Pervasives_Native.Some uu____19880 ->
                                 FStar_Pervasives_Native.Some true
                             | uu____19881 ->
                                 FStar_Pervasives_Native.Some false
                              in
                           (head5, action_unfolded)
                       | uu____19886 -> (head4, FStar_Pervasives_Native.None)
                        in
                     ((let uu____19892 = FStar_Options.defensive ()  in
                       if uu____19892
                       then
                         let is_arg_impure uu____19904 =
                           match uu____19904 with
                           | (e,q) ->
                               let uu____19917 =
                                 let uu____19918 =
                                   FStar_Syntax_Subst.compress e  in
                                 uu____19918.FStar_Syntax_Syntax.n  in
                               (match uu____19917 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                     (m1,m2,t'))
                                    ->
                                    let uu____19933 =
                                      FStar_Syntax_Util.is_pure_effect m1  in
                                    Prims.op_Negation uu____19933
                                | uu____19934 -> false)
                            in
                         let uu____19935 =
                           let uu____19936 =
                             let uu____19947 =
                               FStar_Syntax_Syntax.as_arg head_app  in
                             uu____19947 :: args  in
                           FStar_Util.for_some is_arg_impure uu____19936  in
                         (if uu____19935
                          then
                            let uu____19972 =
                              let uu____19977 =
                                let uu____19978 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____19978
                                 in
                              (FStar_Errors.Warning_Defensive, uu____19977)
                               in
                            FStar_Errors.log_issue
                              head3.FStar_Syntax_Syntax.pos uu____19972
                          else ())
                       else ());
                      (let uu____19981 = maybe_unfold_action head_app  in
                       match uu____19981 with
                       | (head_app1,found_action) ->
                           let mk1 tm =
                             FStar_Syntax_Syntax.mk tm
                               FStar_Pervasives_Native.None
                               head3.FStar_Syntax_Syntax.pos
                              in
                           let body =
                             mk1
                               (FStar_Syntax_Syntax.Tm_app (head_app1, args))
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
                             | FStar_Pervasives_Native.Some (true ) -> body
                              in
                           (log cfg
                              (fun uu____20026  ->
                                 let uu____20027 =
                                   FStar_Syntax_Print.term_to_string head0
                                    in
                                 let uu____20028 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                   uu____20027 uu____20028);
                            (let uu____20029 = FStar_List.tl stack  in
                             norm cfg env uu____20029 body1))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____20031) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____20055 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____20055  in
                     (log cfg
                        (fun uu____20059  ->
                           let uu____20060 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____20060);
                      (let uu____20061 = FStar_List.tl stack  in
                       norm cfg env uu____20061 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____20182  ->
                               match uu____20182 with
                               | (pat,wopt,tm) ->
                                   let uu____20230 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____20230)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____20262 = FStar_List.tl stack  in
                     norm cfg env uu____20262 tm
                 | uu____20263 -> fallback ())

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
              (fun uu____20277  ->
                 let uu____20278 = FStar_Ident.string_of_lid msrc  in
                 let uu____20279 = FStar_Ident.string_of_lid mtgt  in
                 let uu____20280 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____20278
                   uu____20279 uu____20280);
            (let uu____20281 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____20281
             then
               let ed =
                 let uu____20283 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____20283  in
               let uu____20284 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____20284 with
               | (uu____20285,return_repr) ->
                   let return_inst =
                     let uu____20298 =
                       let uu____20299 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____20299.FStar_Syntax_Syntax.n  in
                     match uu____20298 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____20305::[]) ->
                         let uu____20310 =
                           let uu____20317 =
                             let uu____20318 =
                               let uu____20325 =
                                 let uu____20326 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____20326]  in
                               (return_tm, uu____20325)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____20318  in
                           FStar_Syntax_Syntax.mk uu____20317  in
                         uu____20310 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____20332 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____20335 =
                     let uu____20342 =
                       let uu____20343 =
                         let uu____20360 =
                           let uu____20371 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____20380 =
                             let uu____20391 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____20391]  in
                           uu____20371 :: uu____20380  in
                         (return_inst, uu____20360)  in
                       FStar_Syntax_Syntax.Tm_app uu____20343  in
                     FStar_Syntax_Syntax.mk uu____20342  in
                   uu____20335 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____20440 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____20440 with
                | FStar_Pervasives_Native.None  ->
                    let uu____20443 =
                      let uu____20444 = FStar_Ident.text_of_lid msrc  in
                      let uu____20445 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____20444 uu____20445
                       in
                    failwith uu____20443
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____20446;
                      FStar_TypeChecker_Env.mtarget = uu____20447;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____20448;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____20470 =
                      let uu____20471 = FStar_Ident.text_of_lid msrc  in
                      let uu____20472 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____20471 uu____20472
                       in
                    failwith uu____20470
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____20473;
                      FStar_TypeChecker_Env.mtarget = uu____20474;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____20475;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____20510 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____20511 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____20510 t FStar_Syntax_Syntax.tun uu____20511))

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
                (fun uu____20581  ->
                   match uu____20581 with
                   | (a,imp) ->
                       let uu____20600 = norm cfg env [] a  in
                       (uu____20600, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____20610  ->
             let uu____20611 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____20612 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____20611 uu____20612);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20636 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____20636
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___338_20639 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___338_20639.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___338_20639.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20661 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____20661
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___339_20664 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___339_20664.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___339_20664.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____20709  ->
                      match uu____20709 with
                      | (a,i) ->
                          let uu____20728 = norm cfg env [] a  in
                          (uu____20728, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___254_20750  ->
                       match uu___254_20750 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____20754 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____20754
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___340_20762 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___341_20765 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___341_20765.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___340_20762.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___340_20762.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____20768  ->
        match uu____20768 with
        | (x,imp) ->
            let uu____20775 =
              let uu___342_20776 = x  in
              let uu____20777 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___342_20776.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___342_20776.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____20777
              }  in
            (uu____20775, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____20785 =
          FStar_List.fold_left
            (fun uu____20819  ->
               fun b  ->
                 match uu____20819 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____20785 with | (nbs,uu____20899) -> FStar_List.rev nbs

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
            let uu____20931 =
              let uu___343_20932 = rc  in
              let uu____20933 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___343_20932.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____20933;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___343_20932.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____20931
        | uu____20942 -> lopt

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
            (let uu____20965 = FStar_Syntax_Print.term_to_string tm  in
             let uu____20966 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____20965
               uu____20966)
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
          let uu____20992 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____20992
          then tm1
          else
            (let w t =
               let uu___344_21006 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___344_21006.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___344_21006.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____21017 =
                 let uu____21018 = FStar_Syntax_Util.unmeta t  in
                 uu____21018.FStar_Syntax_Syntax.n  in
               match uu____21017 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____21025 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____21086)::args1,(bv,uu____21089)::bs1) ->
                   let uu____21143 =
                     let uu____21144 = FStar_Syntax_Subst.compress t  in
                     uu____21144.FStar_Syntax_Syntax.n  in
                   (match uu____21143 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____21148 -> false)
               | ([],[]) -> true
               | (uu____21177,uu____21178) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____21227 = FStar_Syntax_Print.term_to_string t  in
                  let uu____21228 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____21227
                    uu____21228)
               else ();
               (let uu____21230 = FStar_Syntax_Util.head_and_args' t  in
                match uu____21230 with
                | (hd1,args) ->
                    let uu____21269 =
                      let uu____21270 = FStar_Syntax_Subst.compress hd1  in
                      uu____21270.FStar_Syntax_Syntax.n  in
                    (match uu____21269 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____21277 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____21278 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____21279 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____21277 uu____21278 uu____21279)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____21281 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____21298 = FStar_Syntax_Print.term_to_string t  in
                  let uu____21299 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____21298
                    uu____21299)
               else ();
               (let uu____21301 = FStar_Syntax_Util.is_squash t  in
                match uu____21301 with
                | FStar_Pervasives_Native.Some (uu____21312,t') ->
                    is_applied bs t'
                | uu____21324 ->
                    let uu____21333 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____21333 with
                     | FStar_Pervasives_Native.Some (uu____21344,t') ->
                         is_applied bs t'
                     | uu____21356 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____21380 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____21380 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____21387)::(q,uu____21389)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____21431 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____21432 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____21431 uu____21432)
                    else ();
                    (let uu____21434 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____21434 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21439 =
                           let uu____21440 = FStar_Syntax_Subst.compress p
                              in
                           uu____21440.FStar_Syntax_Syntax.n  in
                         (match uu____21439 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____21448 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____21448))
                          | uu____21451 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____21454)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____21479 =
                           let uu____21480 = FStar_Syntax_Subst.compress p1
                              in
                           uu____21480.FStar_Syntax_Syntax.n  in
                         (match uu____21479 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____21488 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____21488))
                          | uu____21491 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____21495 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____21495 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____21500 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____21500 with
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
                                     let uu____21511 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21511))
                               | uu____21514 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____21519)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____21544 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____21544 with
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
                                     let uu____21555 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21555))
                               | uu____21558 -> FStar_Pervasives_Native.None)
                          | uu____21561 -> FStar_Pervasives_Native.None)
                     | uu____21564 -> FStar_Pervasives_Native.None))
               | uu____21567 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____21580 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____21580 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____21586)::[],uu____21587,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____21606 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____21607 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____21606
                         uu____21607)
                    else ();
                    is_quantified_const bv phi')
               | uu____21609 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____21622 =
                 let uu____21623 = FStar_Syntax_Subst.compress phi  in
                 uu____21623.FStar_Syntax_Syntax.n  in
               match uu____21622 with
               | FStar_Syntax_Syntax.Tm_match (uu____21628,br::brs) ->
                   let uu____21695 = br  in
                   (match uu____21695 with
                    | (uu____21712,uu____21713,e) ->
                        let r =
                          let uu____21734 = simp_t e  in
                          match uu____21734 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____21740 =
                                FStar_List.for_all
                                  (fun uu____21758  ->
                                     match uu____21758 with
                                     | (uu____21771,uu____21772,e') ->
                                         let uu____21786 = simp_t e'  in
                                         uu____21786 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____21740
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____21794 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____21803 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____21803
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____21838 =
                 match uu____21838 with
                 | (t1,q) ->
                     let uu____21859 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____21859 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____21891 -> (t1, q))
                  in
               let uu____21904 = FStar_Syntax_Util.head_and_args t  in
               match uu____21904 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____21982 =
                 let uu____21983 = FStar_Syntax_Util.unmeta ty  in
                 uu____21983.FStar_Syntax_Syntax.n  in
               match uu____21982 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____21987) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____21992,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____22016 -> false  in
             let simplify1 arg =
               let uu____22047 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____22047, arg)  in
             let uu____22060 = is_forall_const tm1  in
             match uu____22060 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____22065 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____22066 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____22065
                       uu____22066)
                  else ();
                  (let uu____22068 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____22068))
             | FStar_Pervasives_Native.None  ->
                 let uu____22069 =
                   let uu____22070 = FStar_Syntax_Subst.compress tm1  in
                   uu____22070.FStar_Syntax_Syntax.n  in
                 (match uu____22069 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____22074;
                              FStar_Syntax_Syntax.vars = uu____22075;_},uu____22076);
                         FStar_Syntax_Syntax.pos = uu____22077;
                         FStar_Syntax_Syntax.vars = uu____22078;_},args)
                      ->
                      let uu____22108 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22108
                      then
                        let uu____22109 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22109 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22164)::
                             (uu____22165,(arg,uu____22167))::[] ->
                             maybe_auto_squash arg
                         | (uu____22232,(arg,uu____22234))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22235)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22300)::uu____22301::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22364::(FStar_Pervasives_Native.Some (false
                                         ),uu____22365)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22428 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22444 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22444
                         then
                           let uu____22445 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22445 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22500)::uu____22501::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22564::(FStar_Pervasives_Native.Some (true
                                           ),uu____22565)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22628)::(uu____22629,(arg,uu____22631))::[]
                               -> maybe_auto_squash arg
                           | (uu____22696,(arg,uu____22698))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22699)::[]
                               -> maybe_auto_squash arg
                           | uu____22764 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22780 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22780
                            then
                              let uu____22781 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22781 with
                              | uu____22836::(FStar_Pervasives_Native.Some
                                              (true ),uu____22837)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22900)::uu____22901::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22964)::(uu____22965,(arg,uu____22967))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23032,(p,uu____23034))::(uu____23035,
                                                                (q,uu____23037))::[]
                                  ->
                                  let uu____23102 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23102
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23104 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23120 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23120
                               then
                                 let uu____23121 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23121 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23176)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23177)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23242)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23243)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23308)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23309)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23374)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23375)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23440,(arg,uu____23442))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23443)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23508)::(uu____23509,(arg,uu____23511))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23576,(arg,uu____23578))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23579)::[]
                                     ->
                                     let uu____23644 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23644
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23645)::(uu____23646,(arg,uu____23648))::[]
                                     ->
                                     let uu____23713 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23713
                                 | (uu____23714,(p,uu____23716))::(uu____23717,
                                                                   (q,uu____23719))::[]
                                     ->
                                     let uu____23784 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23784
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23786 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23802 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23802
                                  then
                                    let uu____23803 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23803 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23858)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23897)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23936 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23952 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23952
                                     then
                                       match args with
                                       | (t,uu____23954)::[] ->
                                           let uu____23979 =
                                             let uu____23980 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23980.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23979 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23983::[],body,uu____23985)
                                                ->
                                                let uu____24020 = simp_t body
                                                   in
                                                (match uu____24020 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24023 -> tm1)
                                            | uu____24026 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24028))::(t,uu____24030)::[]
                                           ->
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
                                                let uu____24110 = simp_t body
                                                   in
                                                (match uu____24110 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24113 -> tm1)
                                            | uu____24116 -> tm1)
                                       | uu____24117 -> tm1
                                     else
                                       (let uu____24129 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24129
                                        then
                                          match args with
                                          | (t,uu____24131)::[] ->
                                              let uu____24156 =
                                                let uu____24157 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24157.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24156 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24160::[],body,uu____24162)
                                                   ->
                                                   let uu____24197 =
                                                     simp_t body  in
                                                   (match uu____24197 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24200 -> tm1)
                                               | uu____24203 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24205))::(t,uu____24207)::[]
                                              ->
                                              let uu____24246 =
                                                let uu____24247 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24247.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24246 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24250::[],body,uu____24252)
                                                   ->
                                                   let uu____24287 =
                                                     simp_t body  in
                                                   (match uu____24287 with
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
                                                    | uu____24290 -> tm1)
                                               | uu____24293 -> tm1)
                                          | uu____24294 -> tm1
                                        else
                                          (let uu____24306 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24306
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24307;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24308;_},uu____24309)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24334;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24335;_},uu____24336)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24361 -> tm1
                                           else
                                             (let uu____24373 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____24373 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____24393 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____24405;
                         FStar_Syntax_Syntax.vars = uu____24406;_},args)
                      ->
                      let uu____24432 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____24432
                      then
                        let uu____24433 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____24433 with
                         | (FStar_Pervasives_Native.Some (true ),uu____24488)::
                             (uu____24489,(arg,uu____24491))::[] ->
                             maybe_auto_squash arg
                         | (uu____24556,(arg,uu____24558))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____24559)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____24624)::uu____24625::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____24688::(FStar_Pervasives_Native.Some (false
                                         ),uu____24689)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____24752 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____24768 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____24768
                         then
                           let uu____24769 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____24769 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____24824)::uu____24825::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____24888::(FStar_Pervasives_Native.Some (true
                                           ),uu____24889)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____24952)::(uu____24953,(arg,uu____24955))::[]
                               -> maybe_auto_squash arg
                           | (uu____25020,(arg,uu____25022))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____25023)::[]
                               -> maybe_auto_squash arg
                           | uu____25088 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____25104 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____25104
                            then
                              let uu____25105 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____25105 with
                              | uu____25160::(FStar_Pervasives_Native.Some
                                              (true ),uu____25161)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____25224)::uu____25225::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____25288)::(uu____25289,(arg,uu____25291))::[]
                                  -> maybe_auto_squash arg
                              | (uu____25356,(p,uu____25358))::(uu____25359,
                                                                (q,uu____25361))::[]
                                  ->
                                  let uu____25426 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____25426
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____25428 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____25444 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____25444
                               then
                                 let uu____25445 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____25445 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25500)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25501)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25566)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25567)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25632)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25633)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25698)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25699)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____25764,(arg,uu____25766))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____25767)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25832)::(uu____25833,(arg,uu____25835))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____25900,(arg,uu____25902))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____25903)::[]
                                     ->
                                     let uu____25968 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25968
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25969)::(uu____25970,(arg,uu____25972))::[]
                                     ->
                                     let uu____26037 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____26037
                                 | (uu____26038,(p,uu____26040))::(uu____26041,
                                                                   (q,uu____26043))::[]
                                     ->
                                     let uu____26108 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____26108
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____26110 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____26126 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____26126
                                  then
                                    let uu____26127 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____26127 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____26182)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____26221)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____26260 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____26276 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____26276
                                     then
                                       match args with
                                       | (t,uu____26278)::[] ->
                                           let uu____26303 =
                                             let uu____26304 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____26304.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____26303 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____26307::[],body,uu____26309)
                                                ->
                                                let uu____26344 = simp_t body
                                                   in
                                                (match uu____26344 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____26347 -> tm1)
                                            | uu____26350 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____26352))::(t,uu____26354)::[]
                                           ->
                                           let uu____26393 =
                                             let uu____26394 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____26394.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____26393 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____26397::[],body,uu____26399)
                                                ->
                                                let uu____26434 = simp_t body
                                                   in
                                                (match uu____26434 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____26437 -> tm1)
                                            | uu____26440 -> tm1)
                                       | uu____26441 -> tm1
                                     else
                                       (let uu____26453 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____26453
                                        then
                                          match args with
                                          | (t,uu____26455)::[] ->
                                              let uu____26480 =
                                                let uu____26481 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26481.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26480 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26484::[],body,uu____26486)
                                                   ->
                                                   let uu____26521 =
                                                     simp_t body  in
                                                   (match uu____26521 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____26524 -> tm1)
                                               | uu____26527 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____26529))::(t,uu____26531)::[]
                                              ->
                                              let uu____26570 =
                                                let uu____26571 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26571.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26570 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26574::[],body,uu____26576)
                                                   ->
                                                   let uu____26611 =
                                                     simp_t body  in
                                                   (match uu____26611 with
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
                                                    | uu____26614 -> tm1)
                                               | uu____26617 -> tm1)
                                          | uu____26618 -> tm1
                                        else
                                          (let uu____26630 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____26630
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26631;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26632;_},uu____26633)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26658;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26659;_},uu____26660)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____26685 -> tm1
                                           else
                                             (let uu____26697 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____26697 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____26717 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____26734 = simp_t t  in
                      (match uu____26734 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____26737 ->
                      let uu____26760 = is_const_match tm1  in
                      (match uu____26760 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____26763 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____26773  ->
               (let uu____26775 = FStar_Syntax_Print.tag_of_term t  in
                let uu____26776 = FStar_Syntax_Print.term_to_string t  in
                let uu____26777 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____26784 =
                  let uu____26785 =
                    let uu____26788 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____26788
                     in
                  stack_to_string uu____26785  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____26775 uu____26776 uu____26777 uu____26784);
               (let uu____26811 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____26811
                then
                  let uu____26812 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____26812 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____26819 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____26820 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____26821 =
                          let uu____26822 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____26822
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____26819
                          uu____26820 uu____26821);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____26840 =
                     let uu____26841 =
                       let uu____26842 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____26842  in
                     FStar_Util.string_of_int uu____26841  in
                   let uu____26847 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____26848 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____26840 uu____26847 uu____26848)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____26854,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____26905  ->
                     let uu____26906 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____26906);
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
               let uu____26944 =
                 let uu___345_26945 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___345_26945.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___345_26945.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____26944
           | (Arg (Univ uu____26948,uu____26949,uu____26950))::uu____26951 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____26954,uu____26955))::uu____26956 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____26971,uu____26972),aq,r))::stack1
               when
               let uu____27022 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____27022 ->
               let t2 =
                 let uu____27026 =
                   let uu____27031 =
                     let uu____27032 = closure_as_term cfg env_arg tm  in
                     (uu____27032, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____27031  in
                 uu____27026 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____27044),aq,r))::stack1 ->
               (log cfg
                  (fun uu____27097  ->
                     let uu____27098 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____27098);
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
                  (let uu____27112 = FStar_ST.op_Bang m  in
                   match uu____27112 with
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
                   | FStar_Pervasives_Native.Some (uu____27253,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____27308 =
                 log cfg
                   (fun uu____27312  ->
                      let uu____27313 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____27313);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____27321 =
                 let uu____27322 = FStar_Syntax_Subst.compress t1  in
                 uu____27322.FStar_Syntax_Syntax.n  in
               (match uu____27321 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____27349 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____27349  in
                    (log cfg
                       (fun uu____27353  ->
                          let uu____27354 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____27354);
                     (let uu____27355 = FStar_List.tl stack  in
                      norm cfg env1 uu____27355 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____27356);
                       FStar_Syntax_Syntax.pos = uu____27357;
                       FStar_Syntax_Syntax.vars = uu____27358;_},(e,uu____27360)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____27399 when
                    (cfg.steps).primops ->
                    let uu____27416 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____27416 with
                     | (hd1,args) ->
                         let uu____27459 =
                           let uu____27460 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____27460.FStar_Syntax_Syntax.n  in
                         (match uu____27459 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____27464 = find_prim_step cfg fv  in
                              (match uu____27464 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____27467; arity = uu____27468;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____27470;
                                     requires_binder_substitution =
                                       uu____27471;
                                     interpretation = uu____27472;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____27489 -> fallback " (3)" ())
                          | uu____27492 -> fallback " (4)" ()))
                | uu____27493 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____27518  ->
                     let uu____27519 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____27519);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____27528 =
                   log cfg1
                     (fun uu____27533  ->
                        let uu____27534 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____27535 =
                          let uu____27536 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____27563  ->
                                    match uu____27563 with
                                    | (p,uu____27573,uu____27574) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____27536
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____27534 uu____27535);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___255_27591  ->
                                match uu___255_27591 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____27592 -> false))
                         in
                      let steps =
                        let uu___346_27594 = cfg1.steps  in
                        {
                          beta = (uu___346_27594.beta);
                          iota = (uu___346_27594.iota);
                          zeta = false;
                          weak = (uu___346_27594.weak);
                          hnf = (uu___346_27594.hnf);
                          primops = (uu___346_27594.primops);
                          do_not_unfold_pure_lets =
                            (uu___346_27594.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___346_27594.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___346_27594.pure_subterms_within_computations);
                          simplify = (uu___346_27594.simplify);
                          erase_universes = (uu___346_27594.erase_universes);
                          allow_unbound_universes =
                            (uu___346_27594.allow_unbound_universes);
                          reify_ = (uu___346_27594.reify_);
                          compress_uvars = (uu___346_27594.compress_uvars);
                          no_full_norm = (uu___346_27594.no_full_norm);
                          check_no_uvars = (uu___346_27594.check_no_uvars);
                          unmeta = (uu___346_27594.unmeta);
                          unascribe = (uu___346_27594.unascribe);
                          in_full_norm_request =
                            (uu___346_27594.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___346_27594.weakly_reduce_scrutinee)
                        }  in
                      let uu___347_27599 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___347_27599.tcenv);
                        debug = (uu___347_27599.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___347_27599.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___347_27599.memoize_lazy);
                        normalize_pure_lets =
                          (uu___347_27599.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____27671 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____27700 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____27784  ->
                                    fun uu____27785  ->
                                      match (uu____27784, uu____27785) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____27924 = norm_pat env3 p1
                                             in
                                          (match uu____27924 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____27700 with
                           | (pats1,env3) ->
                               ((let uu___348_28086 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___348_28086.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___349_28105 = x  in
                            let uu____28106 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___349_28105.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___349_28105.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____28106
                            }  in
                          ((let uu___350_28120 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___350_28120.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___351_28131 = x  in
                            let uu____28132 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___351_28131.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___351_28131.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____28132
                            }  in
                          ((let uu___352_28146 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___352_28146.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___353_28162 = x  in
                            let uu____28163 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___353_28162.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___353_28162.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____28163
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___354_28178 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___354_28178.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____28222 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____28252 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____28252 with
                                  | (p,wopt,e) ->
                                      let uu____28272 = norm_pat env1 p  in
                                      (match uu____28272 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____28327 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____28327
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____28344 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____28344
                      then
                        norm
                          (let uu___355_28349 = cfg1  in
                           {
                             steps =
                               (let uu___356_28352 = cfg1.steps  in
                                {
                                  beta = (uu___356_28352.beta);
                                  iota = (uu___356_28352.iota);
                                  zeta = (uu___356_28352.zeta);
                                  weak = (uu___356_28352.weak);
                                  hnf = (uu___356_28352.hnf);
                                  primops = (uu___356_28352.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___356_28352.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___356_28352.unfold_until);
                                  unfold_only = (uu___356_28352.unfold_only);
                                  unfold_fully =
                                    (uu___356_28352.unfold_fully);
                                  unfold_attr = (uu___356_28352.unfold_attr);
                                  unfold_tac = (uu___356_28352.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___356_28352.pure_subterms_within_computations);
                                  simplify = (uu___356_28352.simplify);
                                  erase_universes =
                                    (uu___356_28352.erase_universes);
                                  allow_unbound_universes =
                                    (uu___356_28352.allow_unbound_universes);
                                  reify_ = (uu___356_28352.reify_);
                                  compress_uvars =
                                    (uu___356_28352.compress_uvars);
                                  no_full_norm =
                                    (uu___356_28352.no_full_norm);
                                  check_no_uvars =
                                    (uu___356_28352.check_no_uvars);
                                  unmeta = (uu___356_28352.unmeta);
                                  unascribe = (uu___356_28352.unascribe);
                                  in_full_norm_request =
                                    (uu___356_28352.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___355_28349.tcenv);
                             debug = (uu___355_28349.debug);
                             delta_level = (uu___355_28349.delta_level);
                             primitive_steps =
                               (uu___355_28349.primitive_steps);
                             strong = (uu___355_28349.strong);
                             memoize_lazy = (uu___355_28349.memoize_lazy);
                             normalize_pure_lets =
                               (uu___355_28349.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____28354 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____28354)
                    in
                 let rec is_cons head1 =
                   let uu____28379 =
                     let uu____28380 = FStar_Syntax_Subst.compress head1  in
                     uu____28380.FStar_Syntax_Syntax.n  in
                   match uu____28379 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____28384) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____28389 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____28390;
                         FStar_Syntax_Syntax.fv_delta = uu____28391;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____28392;
                         FStar_Syntax_Syntax.fv_delta = uu____28393;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____28394);_}
                       -> true
                   | uu____28401 -> false  in
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
                   let uu____28564 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____28564 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____28657 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____28696 ->
                                 let uu____28697 =
                                   let uu____28698 = is_cons head1  in
                                   Prims.op_Negation uu____28698  in
                                 FStar_Util.Inr uu____28697)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____28723 =
                              let uu____28724 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____28724.FStar_Syntax_Syntax.n  in
                            (match uu____28723 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____28742 ->
                                 let uu____28743 =
                                   let uu____28744 = is_cons head1  in
                                   Prims.op_Negation uu____28744  in
                                 FStar_Util.Inr uu____28743))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____28827)::rest_a,(p1,uu____28830)::rest_p) ->
                       let uu____28884 = matches_pat t2 p1  in
                       (match uu____28884 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____28933 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____29053 = matches_pat scrutinee1 p1  in
                       (match uu____29053 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____29093  ->
                                  let uu____29094 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____29095 =
                                    let uu____29096 =
                                      FStar_List.map
                                        (fun uu____29106  ->
                                           match uu____29106 with
                                           | (uu____29111,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____29096
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____29094 uu____29095);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____29143  ->
                                       match uu____29143 with
                                       | (bv,t2) ->
                                           let uu____29166 =
                                             let uu____29173 =
                                               let uu____29176 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____29176
                                                in
                                             let uu____29177 =
                                               let uu____29178 =
                                                 let uu____29209 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____29209, false)
                                                  in
                                               Clos uu____29178  in
                                             (uu____29173, uu____29177)  in
                                           uu____29166 :: env2) env1 s
                                 in
                              let uu____29322 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____29322)))
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
    let uu____29349 =
      let uu____29352 = FStar_ST.op_Bang plugins  in p :: uu____29352  in
    FStar_ST.op_Colon_Equals plugins uu____29349  in
  let retrieve uu____29452 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____29525  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___256_29566  ->
                  match uu___256_29566 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | uu____29570 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____29576 -> d  in
        let uu____29579 = to_fsteps s  in
        let uu____29580 =
          let uu____29581 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____29582 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormTop")  in
          let uu____29583 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormCfg")  in
          let uu____29584 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____29585 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____29586 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____29587 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____29588 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____29589 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____29581;
            top = uu____29582;
            cfg = uu____29583;
            primop = uu____29584;
            unfolding = uu____29585;
            b380 = uu____29586;
            wpe = uu____29587;
            norm_delayed = uu____29588;
            print_normalized = uu____29589
          }  in
        let uu____29590 =
          let uu____29593 =
            let uu____29596 = retrieve_plugins ()  in
            FStar_List.append uu____29596 psteps  in
          add_steps built_in_primitive_steps uu____29593  in
        let uu____29599 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____29601 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____29601)
           in
        {
          steps = uu____29579;
          tcenv = e;
          debug = uu____29580;
          delta_level = d1;
          primitive_steps = uu____29590;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____29599
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
          log_top c
            (fun uu____29650  ->
               let uu____29651 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "Starting normalizer for (%s) {\n"
                 uu____29651);
          (let r = norm c [] [] t  in
           log_top c
             (fun uu____29662  ->
                let uu____29663 = FStar_Syntax_Print.term_to_string r  in
                FStar_Util.print1 "}\nNormalization result = (%s)\n"
                  uu____29663);
           r)
  
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
      fun t  -> let uu____29694 = config s e  in norm_comp uu____29694 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____29711 = config [] env  in norm_universe uu____29711 [] u
  
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
        let uu____29735 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29735  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____29742 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___357_29761 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___357_29761.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___357_29761.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____29768 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____29768
          then
            let ct1 =
              let uu____29770 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____29770 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____29777 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____29777
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___358_29781 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___358_29781.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___358_29781.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___358_29781.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___359_29783 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___359_29783.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___359_29783.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___359_29783.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___359_29783.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___360_29784 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___360_29784.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___360_29784.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____29786 -> c
  
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
        let uu____29804 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29804  in
      let uu____29811 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____29811
      then
        let uu____29812 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____29812 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____29818  ->
                 let uu____29819 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____29819)
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
            ((let uu____29840 =
                let uu____29845 =
                  let uu____29846 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29846
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29845)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____29840);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____29861 = config [AllowUnboundUniverses] env  in
          norm_comp uu____29861 [] c
        with
        | e ->
            ((let uu____29874 =
                let uu____29879 =
                  let uu____29880 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29880
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29879)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____29874);
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
                   let uu____29925 =
                     let uu____29926 =
                       let uu____29933 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____29933)  in
                     FStar_Syntax_Syntax.Tm_refine uu____29926  in
                   mk uu____29925 t01.FStar_Syntax_Syntax.pos
               | uu____29938 -> t2)
          | uu____29939 -> t2  in
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
        let uu____30018 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____30018 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____30055 ->
                 let uu____30064 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____30064 with
                  | (actuals,uu____30074,uu____30075) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____30093 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____30093 with
                         | (binders,args) ->
                             let uu____30104 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____30104
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
      | uu____30118 ->
          let uu____30119 = FStar_Syntax_Util.head_and_args t  in
          (match uu____30119 with
           | (head1,args) ->
               let uu____30162 =
                 let uu____30163 = FStar_Syntax_Subst.compress head1  in
                 uu____30163.FStar_Syntax_Syntax.n  in
               (match uu____30162 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____30184 =
                      let uu____30199 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____30199  in
                    (match uu____30184 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____30237 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___365_30245 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___365_30245.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___365_30245.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___365_30245.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___365_30245.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___365_30245.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___365_30245.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___365_30245.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___365_30245.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___365_30245.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___365_30245.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___365_30245.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___365_30245.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___365_30245.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___365_30245.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___365_30245.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___365_30245.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___365_30245.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___365_30245.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___365_30245.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___365_30245.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___365_30245.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___365_30245.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___365_30245.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___365_30245.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___365_30245.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___365_30245.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___365_30245.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___365_30245.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___365_30245.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___365_30245.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___365_30245.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___365_30245.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___365_30245.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___365_30245.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___365_30245.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___365_30245.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___365_30245.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___365_30245.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____30237 with
                            | (uu____30246,ty,uu____30248) ->
                                eta_expand_with_type env t ty))
                | uu____30249 ->
                    let uu____30250 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___366_30258 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___366_30258.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___366_30258.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___366_30258.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___366_30258.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___366_30258.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___366_30258.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___366_30258.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___366_30258.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___366_30258.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___366_30258.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___366_30258.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___366_30258.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___366_30258.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___366_30258.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___366_30258.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___366_30258.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___366_30258.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___366_30258.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___366_30258.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___366_30258.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___366_30258.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___366_30258.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___366_30258.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___366_30258.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___366_30258.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___366_30258.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___366_30258.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___366_30258.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___366_30258.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___366_30258.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___366_30258.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___366_30258.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___366_30258.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___366_30258.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___366_30258.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___366_30258.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___366_30258.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___366_30258.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____30250 with
                     | (uu____30259,ty,uu____30261) ->
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
      let uu___367_30342 = x  in
      let uu____30343 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___367_30342.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___367_30342.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____30343
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____30346 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____30369 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____30370 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____30371 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____30372 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____30379 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____30380 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____30381 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___368_30415 = rc  in
          let uu____30416 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____30425 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___368_30415.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____30416;
            FStar_Syntax_Syntax.residual_flags = uu____30425
          }  in
        let uu____30428 =
          let uu____30429 =
            let uu____30448 = elim_delayed_subst_binders bs  in
            let uu____30457 = elim_delayed_subst_term t2  in
            let uu____30460 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____30448, uu____30457, uu____30460)  in
          FStar_Syntax_Syntax.Tm_abs uu____30429  in
        mk1 uu____30428
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____30497 =
          let uu____30498 =
            let uu____30513 = elim_delayed_subst_binders bs  in
            let uu____30522 = elim_delayed_subst_comp c  in
            (uu____30513, uu____30522)  in
          FStar_Syntax_Syntax.Tm_arrow uu____30498  in
        mk1 uu____30497
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____30541 =
          let uu____30542 =
            let uu____30549 = elim_bv bv  in
            let uu____30550 = elim_delayed_subst_term phi  in
            (uu____30549, uu____30550)  in
          FStar_Syntax_Syntax.Tm_refine uu____30542  in
        mk1 uu____30541
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____30581 =
          let uu____30582 =
            let uu____30599 = elim_delayed_subst_term t2  in
            let uu____30602 = elim_delayed_subst_args args  in
            (uu____30599, uu____30602)  in
          FStar_Syntax_Syntax.Tm_app uu____30582  in
        mk1 uu____30581
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___369_30674 = p  in
              let uu____30675 =
                let uu____30676 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____30676  in
              {
                FStar_Syntax_Syntax.v = uu____30675;
                FStar_Syntax_Syntax.p =
                  (uu___369_30674.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___370_30678 = p  in
              let uu____30679 =
                let uu____30680 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____30680  in
              {
                FStar_Syntax_Syntax.v = uu____30679;
                FStar_Syntax_Syntax.p =
                  (uu___370_30678.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___371_30687 = p  in
              let uu____30688 =
                let uu____30689 =
                  let uu____30696 = elim_bv x  in
                  let uu____30697 = elim_delayed_subst_term t0  in
                  (uu____30696, uu____30697)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____30689  in
              {
                FStar_Syntax_Syntax.v = uu____30688;
                FStar_Syntax_Syntax.p =
                  (uu___371_30687.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___372_30720 = p  in
              let uu____30721 =
                let uu____30722 =
                  let uu____30735 =
                    FStar_List.map
                      (fun uu____30758  ->
                         match uu____30758 with
                         | (x,b) ->
                             let uu____30771 = elim_pat x  in
                             (uu____30771, b)) pats
                     in
                  (fv, uu____30735)  in
                FStar_Syntax_Syntax.Pat_cons uu____30722  in
              {
                FStar_Syntax_Syntax.v = uu____30721;
                FStar_Syntax_Syntax.p =
                  (uu___372_30720.FStar_Syntax_Syntax.p)
              }
          | uu____30784 -> p  in
        let elim_branch uu____30808 =
          match uu____30808 with
          | (pat,wopt,t3) ->
              let uu____30834 = elim_pat pat  in
              let uu____30837 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____30840 = elim_delayed_subst_term t3  in
              (uu____30834, uu____30837, uu____30840)
           in
        let uu____30845 =
          let uu____30846 =
            let uu____30869 = elim_delayed_subst_term t2  in
            let uu____30872 = FStar_List.map elim_branch branches  in
            (uu____30869, uu____30872)  in
          FStar_Syntax_Syntax.Tm_match uu____30846  in
        mk1 uu____30845
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____31003 =
          match uu____31003 with
          | (tc,topt) ->
              let uu____31038 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____31048 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____31048
                | FStar_Util.Inr c ->
                    let uu____31050 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____31050
                 in
              let uu____31051 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____31038, uu____31051)
           in
        let uu____31060 =
          let uu____31061 =
            let uu____31088 = elim_delayed_subst_term t2  in
            let uu____31091 = elim_ascription a  in
            (uu____31088, uu____31091, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____31061  in
        mk1 uu____31060
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___373_31152 = lb  in
          let uu____31153 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____31156 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___373_31152.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___373_31152.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____31153;
            FStar_Syntax_Syntax.lbeff =
              (uu___373_31152.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____31156;
            FStar_Syntax_Syntax.lbattrs =
              (uu___373_31152.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___373_31152.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____31159 =
          let uu____31160 =
            let uu____31173 =
              let uu____31180 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____31180)  in
            let uu____31189 = elim_delayed_subst_term t2  in
            (uu____31173, uu____31189)  in
          FStar_Syntax_Syntax.Tm_let uu____31160  in
        mk1 uu____31159
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____31233 =
          let uu____31234 =
            let uu____31241 = elim_delayed_subst_term tm  in
            (uu____31241, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____31234  in
        mk1 uu____31233
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____31252 =
          let uu____31253 =
            let uu____31260 = elim_delayed_subst_term t2  in
            let uu____31263 = elim_delayed_subst_meta md  in
            (uu____31260, uu____31263)  in
          FStar_Syntax_Syntax.Tm_meta uu____31253  in
        mk1 uu____31252

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___257_31272  ->
         match uu___257_31272 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____31276 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____31276
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
        let uu____31299 =
          let uu____31300 =
            let uu____31309 = elim_delayed_subst_term t  in
            (uu____31309, uopt)  in
          FStar_Syntax_Syntax.Total uu____31300  in
        mk1 uu____31299
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____31326 =
          let uu____31327 =
            let uu____31336 = elim_delayed_subst_term t  in
            (uu____31336, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____31327  in
        mk1 uu____31326
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___374_31345 = ct  in
          let uu____31346 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____31349 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____31360 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___374_31345.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___374_31345.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____31346;
            FStar_Syntax_Syntax.effect_args = uu____31349;
            FStar_Syntax_Syntax.flags = uu____31360
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___258_31363  ->
    match uu___258_31363 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____31377 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____31377
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____31416 =
          let uu____31423 = elim_delayed_subst_term t  in (m, uu____31423)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____31416
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____31435 =
          let uu____31444 = elim_delayed_subst_term t  in
          (m1, m2, uu____31444)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____31435
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
      (fun uu____31477  ->
         match uu____31477 with
         | (t,q) ->
             let uu____31496 = elim_delayed_subst_term t  in (uu____31496, q))
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
      (fun uu____31524  ->
         match uu____31524 with
         | (x,q) ->
             let uu____31543 =
               let uu___375_31544 = x  in
               let uu____31545 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___375_31544.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___375_31544.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____31545
               }  in
             (uu____31543, q)) bs

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
            | (uu____31651,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____31683,FStar_Util.Inl t) ->
                let uu____31705 =
                  let uu____31712 =
                    let uu____31713 =
                      let uu____31728 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____31728)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____31713  in
                  FStar_Syntax_Syntax.mk uu____31712  in
                uu____31705 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____31744 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____31744 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____31776 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____31849 ->
                    let uu____31850 =
                      let uu____31859 =
                        let uu____31860 = FStar_Syntax_Subst.compress t4  in
                        uu____31860.FStar_Syntax_Syntax.n  in
                      (uu____31859, tc)  in
                    (match uu____31850 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____31889) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____31936) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____31981,FStar_Util.Inl uu____31982) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____32013 -> failwith "Impossible")
                 in
              (match uu____31776 with
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
          let uu____32150 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____32150 with
          | (univ_names1,binders1,tc) ->
              let uu____32224 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____32224)
  
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
          let uu____32277 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____32277 with
          | (univ_names1,binders1,tc) ->
              let uu____32351 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____32351)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____32392 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____32392 with
           | (univ_names1,binders1,typ1) ->
               let uu___376_32432 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___376_32432.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___376_32432.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___376_32432.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___376_32432.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___377_32447 = s  in
          let uu____32448 =
            let uu____32449 =
              let uu____32458 = FStar_List.map (elim_uvars env) sigs  in
              (uu____32458, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____32449  in
          {
            FStar_Syntax_Syntax.sigel = uu____32448;
            FStar_Syntax_Syntax.sigrng =
              (uu___377_32447.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___377_32447.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___377_32447.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___377_32447.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____32475 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32475 with
           | (univ_names1,uu____32499,typ1) ->
               let uu___378_32521 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___378_32521.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___378_32521.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___378_32521.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___378_32521.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____32527 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32527 with
           | (univ_names1,uu____32551,typ1) ->
               let uu___379_32573 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_32573.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_32573.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_32573.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_32573.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____32601 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____32601 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____32626 =
                            let uu____32627 =
                              let uu____32628 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____32628  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____32627
                             in
                          elim_delayed_subst_term uu____32626  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___380_32631 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___380_32631.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___380_32631.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___380_32631.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___380_32631.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___381_32632 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___381_32632.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_32632.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_32632.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_32632.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___382_32638 = s  in
          let uu____32639 =
            let uu____32640 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____32640  in
          {
            FStar_Syntax_Syntax.sigel = uu____32639;
            FStar_Syntax_Syntax.sigrng =
              (uu___382_32638.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_32638.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_32638.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_32638.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____32644 = elim_uvars_aux_t env us [] t  in
          (match uu____32644 with
           | (us1,uu____32668,t1) ->
               let uu___383_32690 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_32690.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_32690.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_32690.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_32690.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____32691 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____32693 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____32693 with
           | (univs1,binders,signature) ->
               let uu____32733 =
                 let uu____32738 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____32738 with
                 | (univs_opening,univs2) ->
                     let uu____32761 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____32761)
                  in
               (match uu____32733 with
                | (univs_opening,univs_closing) ->
                    let uu____32764 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____32770 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____32771 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____32770, uu____32771)  in
                    (match uu____32764 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____32797 =
                           match uu____32797 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____32815 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____32815 with
                                | (us1,t1) ->
                                    let uu____32826 =
                                      let uu____32835 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____32846 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____32835, uu____32846)  in
                                    (match uu____32826 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____32875 =
                                           let uu____32884 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____32895 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____32884, uu____32895)  in
                                         (match uu____32875 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____32925 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____32925
                                                 in
                                              let uu____32926 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____32926 with
                                               | (uu____32953,uu____32954,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____32977 =
                                                       let uu____32978 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____32978
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____32977
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____32987 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____32987 with
                           | (uu____33006,uu____33007,t1) -> t1  in
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
                             | uu____33083 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____33110 =
                               let uu____33111 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____33111.FStar_Syntax_Syntax.n  in
                             match uu____33110 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____33170 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____33203 =
                               let uu____33204 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____33204.FStar_Syntax_Syntax.n  in
                             match uu____33203 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____33227) ->
                                 let uu____33252 = destruct_action_body body
                                    in
                                 (match uu____33252 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____33301 ->
                                 let uu____33302 = destruct_action_body t  in
                                 (match uu____33302 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____33357 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____33357 with
                           | (action_univs,t) ->
                               let uu____33366 = destruct_action_typ_templ t
                                  in
                               (match uu____33366 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___384_33413 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___384_33413.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___384_33413.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___385_33415 = ed  in
                           let uu____33416 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____33417 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____33418 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____33419 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____33420 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____33421 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____33422 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____33423 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____33424 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____33425 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____33426 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____33427 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____33428 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____33429 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___385_33415.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___385_33415.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____33416;
                             FStar_Syntax_Syntax.bind_wp = uu____33417;
                             FStar_Syntax_Syntax.if_then_else = uu____33418;
                             FStar_Syntax_Syntax.ite_wp = uu____33419;
                             FStar_Syntax_Syntax.stronger = uu____33420;
                             FStar_Syntax_Syntax.close_wp = uu____33421;
                             FStar_Syntax_Syntax.assert_p = uu____33422;
                             FStar_Syntax_Syntax.assume_p = uu____33423;
                             FStar_Syntax_Syntax.null_wp = uu____33424;
                             FStar_Syntax_Syntax.trivial = uu____33425;
                             FStar_Syntax_Syntax.repr = uu____33426;
                             FStar_Syntax_Syntax.return_repr = uu____33427;
                             FStar_Syntax_Syntax.bind_repr = uu____33428;
                             FStar_Syntax_Syntax.actions = uu____33429;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___385_33415.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___386_33432 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___386_33432.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___386_33432.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___386_33432.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___386_33432.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___259_33453 =
            match uu___259_33453 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____33484 = elim_uvars_aux_t env us [] t  in
                (match uu____33484 with
                 | (us1,uu____33516,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___387_33547 = sub_eff  in
            let uu____33548 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____33551 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___387_33547.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___387_33547.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____33548;
              FStar_Syntax_Syntax.lift = uu____33551
            }  in
          let uu___388_33554 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___388_33554.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___388_33554.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___388_33554.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___388_33554.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____33564 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____33564 with
           | (univ_names1,binders1,comp1) ->
               let uu___389_33604 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___389_33604.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___389_33604.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___389_33604.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___389_33604.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____33607 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____33608 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  