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
          | FStar_Pervasives_Native.Some uu____3139 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3211 =
      FStar_List.map
        (fun uu____3225  ->
           match uu____3225 with
           | (bopt,c) ->
               let uu____3238 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3240 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3238 uu____3240) env
       in
    FStar_All.pipe_right uu____3211 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___242_3243  ->
    match uu___242_3243 with
    | Clos (env,t,uu____3246,uu____3247) ->
        let uu____3292 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3299 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3292 uu____3299
    | Univ uu____3300 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___243_3305  ->
    match uu___243_3305 with
    | Arg (c,uu____3307,uu____3308) ->
        let uu____3309 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3309
    | MemoLazy uu____3310 -> "MemoLazy"
    | Abs (uu____3317,bs,uu____3319,uu____3320,uu____3321) ->
        let uu____3326 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3326
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
  fun uu___244_3443  ->
    match uu___244_3443 with | [] -> true | uu____3446 -> false
  
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
            (fun uu____3927  ->
               let uu____3928 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3929 = env_to_string env  in
               let uu____3930 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3928 uu____3929 uu____3930);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3939 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3942 ->
                    let uu____3965 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3965
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3966 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3967 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3968 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3969 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3993 ->
                           let uu____4006 =
                             let uu____4007 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____4008 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____4007 uu____4008
                              in
                           failwith uu____4006
                       | uu____4011 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___245_4046  ->
                                         match uu___245_4046 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4053 =
                                               let uu____4060 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4060)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4053
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___289_4070 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___289_4070.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___289_4070.FStar_Syntax_Syntax.sort)
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
                                              | uu____4075 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4078 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___290_4082 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___290_4082.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___290_4082.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4103 =
                        let uu____4104 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4104  in
                      mk uu____4103 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4112 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4112  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4114 = lookup_bvar env x  in
                    (match uu____4114 with
                     | Univ uu____4117 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___291_4121 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___291_4121.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___291_4121.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4127,uu____4128) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4217  ->
                              fun stack1  ->
                                match uu____4217 with
                                | (a,aq) ->
                                    let uu____4229 =
                                      let uu____4230 =
                                        let uu____4237 =
                                          let uu____4238 =
                                            let uu____4269 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4269, false)  in
                                          Clos uu____4238  in
                                        (uu____4237, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4230  in
                                    uu____4229 :: stack1) args)
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
                    let uu____4457 = close_binders cfg env bs  in
                    (match uu____4457 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4512 =
                      let uu____4525 =
                        let uu____4534 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4534]  in
                      close_binders cfg env uu____4525  in
                    (match uu____4512 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4579 =
                             let uu____4580 =
                               let uu____4587 =
                                 let uu____4588 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4588
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4587, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4580  in
                           mk uu____4579 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4687 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4687
                      | FStar_Util.Inr c ->
                          let uu____4701 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4701
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4720 =
                        let uu____4721 =
                          let uu____4748 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4748, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4721  in
                      mk uu____4720 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4794 =
                            let uu____4795 =
                              let uu____4802 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4802, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4795  in
                          mk uu____4794 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4854  -> dummy :: env1) env
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
                    let uu____4875 =
                      let uu____4886 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4886
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4905 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___292_4921 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___292_4921.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___292_4921.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4905))
                       in
                    (match uu____4875 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___293_4939 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___293_4939.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___293_4939.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___293_4939.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___293_4939.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4953,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____5016  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____5033 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5033
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5045  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5069 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5069
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___294_5077 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___294_5077.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___294_5077.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___295_5078 = lb  in
                      let uu____5079 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___295_5078.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___295_5078.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5079;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___295_5078.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___295_5078.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5111  -> fun env1  -> dummy :: env1)
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
            (fun uu____5200  ->
               let uu____5201 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5202 = env_to_string env  in
               let uu____5203 = stack_to_string stack  in
               let uu____5204 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5201 uu____5202 uu____5203 uu____5204);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5209,uu____5210),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5289 = close_binders cfg env' bs  in
               (match uu____5289 with
                | (bs1,uu____5305) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5325 =
                      let uu___296_5328 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___296_5328.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___296_5328.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5325)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5384 =
                 match uu____5384 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5499 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5528 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5612  ->
                                     fun uu____5613  ->
                                       match (uu____5612, uu____5613) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5752 = norm_pat env4 p1
                                              in
                                           (match uu____5752 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5528 with
                            | (pats1,env4) ->
                                ((let uu___297_5914 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___297_5914.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___298_5933 = x  in
                             let uu____5934 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___298_5933.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___298_5933.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5934
                             }  in
                           ((let uu___299_5948 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___299_5948.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___300_5959 = x  in
                             let uu____5960 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___300_5959.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___300_5959.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5960
                             }  in
                           ((let uu___301_5974 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___301_5974.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___302_5990 = x  in
                             let uu____5991 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___302_5990.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___302_5990.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5991
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___303_6008 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___303_6008.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____6013 = norm_pat env2 pat  in
                     (match uu____6013 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____6082 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____6082
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6101 =
                   let uu____6102 =
                     let uu____6125 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6125)  in
                   FStar_Syntax_Syntax.Tm_match uu____6102  in
                 mk uu____6101 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6240 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6349  ->
                                       match uu____6349 with
                                       | (a,q) ->
                                           let uu____6376 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6376, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6240
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6389 =
                       let uu____6396 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6396)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6389
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6408 =
                       let uu____6417 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6417)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6408
                 | uu____6422 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6428 -> failwith "Impossible: unexpected stack element")

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
        let uu____6444 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6527  ->
                  fun uu____6528  ->
                    match (uu____6527, uu____6528) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___304_6668 = b  in
                          let uu____6669 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___304_6668.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___304_6668.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6669
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6444 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6806 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6819 = inline_closure_env cfg env [] t  in
                 let uu____6820 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6819 uu____6820
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6833 = inline_closure_env cfg env [] t  in
                 let uu____6834 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6833 uu____6834
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6888  ->
                           match uu____6888 with
                           | (a,q) ->
                               let uu____6909 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6909, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___246_6926  ->
                           match uu___246_6926 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6930 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6930
                           | f -> f))
                    in
                 let uu____6934 =
                   let uu___305_6935 = c1  in
                   let uu____6936 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6936;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___305_6935.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6934)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___247_6946  ->
            match uu___247_6946 with
            | FStar_Syntax_Syntax.DECREASES uu____6947 -> false
            | uu____6950 -> true))

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
                   (fun uu___248_6968  ->
                      match uu___248_6968 with
                      | FStar_Syntax_Syntax.DECREASES uu____6969 -> false
                      | uu____6972 -> true))
               in
            let rc1 =
              let uu___306_6974 = rc  in
              let uu____6975 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___306_6974.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6975;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6984 -> lopt

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
    let uu____7101 =
      let uu____7110 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____7110  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____7101  in
  let arg_as_bounded_int uu____7140 =
    match uu____7140 with
    | (a,uu____7154) ->
        let uu____7165 =
          let uu____7166 = FStar_Syntax_Subst.compress a  in
          uu____7166.FStar_Syntax_Syntax.n  in
        (match uu____7165 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____7176;
                FStar_Syntax_Syntax.vars = uu____7177;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____7179;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____7180;_},uu____7181)::[])
             when
             let uu____7230 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7230 "int_to_t" ->
             let uu____7231 =
               let uu____7236 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7236)  in
             FStar_Pervasives_Native.Some uu____7231
         | uu____7241 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7289 = f a  in FStar_Pervasives_Native.Some uu____7289
    | uu____7290 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7346 = f a0 a1  in FStar_Pervasives_Native.Some uu____7346
    | uu____7347 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7405 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7405  in
  let binary_op as_a f res args =
    let uu____7478 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7478  in
  let as_primitive_step is_strong uu____7517 =
    match uu____7517 with
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
           let uu____7577 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7577)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7613 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7613)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7642 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7642)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7678 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7678)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7714 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7714)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7856 =
          let uu____7865 = as_a a  in
          let uu____7868 = as_b b  in (uu____7865, uu____7868)  in
        (match uu____7856 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7883 =
               let uu____7884 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7884  in
             FStar_Pervasives_Native.Some uu____7883
         | uu____7885 -> FStar_Pervasives_Native.None)
    | uu____7894 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7914 =
        let uu____7915 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7915  in
      mk uu____7914 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7929 =
      let uu____7932 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7932  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7929  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7974 =
      let uu____7975 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7975  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7974
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____8053 = arg_as_string a1  in
        (match uu____8053 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8059 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____8059 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8072 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____8072
              | uu____8073 -> FStar_Pervasives_Native.None)
         | uu____8078 -> FStar_Pervasives_Native.None)
    | uu____8081 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____8103 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____8103
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8140 =
          let uu____8161 = arg_as_string fn  in
          let uu____8164 = arg_as_int from_line  in
          let uu____8167 = arg_as_int from_col  in
          let uu____8170 = arg_as_int to_line  in
          let uu____8173 = arg_as_int to_col  in
          (uu____8161, uu____8164, uu____8167, uu____8170, uu____8173)  in
        (match uu____8140 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8204 =
                 let uu____8205 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8206 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8205 uu____8206  in
               let uu____8207 =
                 let uu____8208 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8209 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8208 uu____8209  in
               FStar_Range.mk_range fn1 uu____8204 uu____8207  in
             let uu____8210 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8210
         | uu____8211 -> FStar_Pervasives_Native.None)
    | uu____8232 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8265)::(a1,uu____8267)::(a2,uu____8269)::[] ->
        let uu____8326 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8326 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8331 -> FStar_Pervasives_Native.None)
    | uu____8332 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8367)::[] ->
        let uu____8384 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8384 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8390 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8390
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8391 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8419 =
      let uu____8436 =
        let uu____8453 =
          let uu____8470 =
            let uu____8487 =
              let uu____8504 =
                let uu____8521 =
                  let uu____8538 =
                    let uu____8555 =
                      let uu____8572 =
                        let uu____8589 =
                          let uu____8606 =
                            let uu____8623 =
                              let uu____8640 =
                                let uu____8657 =
                                  let uu____8674 =
                                    let uu____8691 =
                                      let uu____8708 =
                                        let uu____8725 =
                                          let uu____8742 =
                                            let uu____8759 =
                                              let uu____8776 =
                                                let uu____8791 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8791,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8800 =
                                                let uu____8817 =
                                                  let uu____8832 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8832,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8845 =
                                                  let uu____8862 =
                                                    let uu____8877 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8877,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8886 =
                                                    let uu____8903 =
                                                      let uu____8918 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8918,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8903]  in
                                                  uu____8862 :: uu____8886
                                                   in
                                                uu____8817 :: uu____8845  in
                                              uu____8776 :: uu____8800  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8759
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8742
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8725
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8708
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8691
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____9138 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____9138 y)))
                                    :: uu____8674
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8657
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8640
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8623
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8606
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8589
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8572
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9333 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9333)))
                      :: uu____8555
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9363 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9363)))
                    :: uu____8538
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9393 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9393)))
                  :: uu____8521
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9423 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9423)))
                :: uu____8504
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8487
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8470
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8453
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8436
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8419
     in
  let weak_ops =
    let uu____9578 =
      let uu____9593 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9593, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9578]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9673 =
        let uu____9678 =
          let uu____9679 = FStar_Syntax_Syntax.as_arg c  in [uu____9679]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9678  in
      uu____9673 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9759 =
                let uu____9774 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9774, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9796  ->
                          fun uu____9797  ->
                            match (uu____9796, uu____9797) with
                            | ((int_to_t1,x),(uu____9816,y)) ->
                                let uu____9826 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9826)))
                 in
              let uu____9827 =
                let uu____9844 =
                  let uu____9859 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9859, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9881  ->
                            fun uu____9882  ->
                              match (uu____9881, uu____9882) with
                              | ((int_to_t1,x),(uu____9901,y)) ->
                                  let uu____9911 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9911)))
                   in
                let uu____9912 =
                  let uu____9929 =
                    let uu____9944 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9944, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9966  ->
                              fun uu____9967  ->
                                match (uu____9966, uu____9967) with
                                | ((int_to_t1,x),(uu____9986,y)) ->
                                    let uu____9996 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9996)))
                     in
                  let uu____9997 =
                    let uu____10014 =
                      let uu____10029 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____10029, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____10047  ->
                                match uu____10047 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____10014]  in
                  uu____9929 :: uu____9997  in
                uu____9844 :: uu____9912  in
              uu____9759 :: uu____9827))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____10177 =
                let uu____10192 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____10192, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____10214  ->
                          fun uu____10215  ->
                            match (uu____10214, uu____10215) with
                            | ((int_to_t1,x),(uu____10234,y)) ->
                                let uu____10244 =
                                  FStar_BigInt.div_big_int x y  in
                                int_as_bounded r int_to_t1 uu____10244)))
                 in
              let uu____10245 =
                let uu____10262 =
                  let uu____10277 =
                    FStar_Parser_Const.p2l ["FStar"; m; "rem"]  in
                  (uu____10277, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____10299  ->
                            fun uu____10300  ->
                              match (uu____10299, uu____10300) with
                              | ((int_to_t1,x),(uu____10319,y)) ->
                                  let uu____10329 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10329)))
                   in
                [uu____10262]  in
              uu____10177 :: uu____10245))
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
    | (_typ,uu____10459)::(a1,uu____10461)::(a2,uu____10463)::[] ->
        let uu____10520 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10520 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___307_10524 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___307_10524.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___307_10524.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___308_10526 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___308_10526.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___308_10526.FStar_Syntax_Syntax.vars)
                })
         | uu____10527 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10529)::uu____10530::(a1,uu____10532)::(a2,uu____10534)::[]
        ->
        let uu____10607 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10607 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___307_10611 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___307_10611.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___307_10611.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___308_10613 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___308_10613.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___308_10613.FStar_Syntax_Syntax.vars)
                })
         | uu____10614 -> FStar_Pervasives_Native.None)
    | uu____10615 -> failwith "Unexpected number of arguments"  in
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
    let uu____10669 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10669 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10717 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10717) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10779  ->
           fun subst1  ->
             match uu____10779 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10820,uu____10821)) ->
                      let uu____10880 = b  in
                      (match uu____10880 with
                       | (bv,uu____10888) ->
                           let uu____10889 =
                             let uu____10890 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10890  in
                           if uu____10889
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10895 = unembed_binder term1  in
                              match uu____10895 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10902 =
                                      let uu___309_10903 = bv  in
                                      let uu____10904 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___309_10903.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___309_10903.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10904
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10902
                                     in
                                  let b_for_x =
                                    let uu____10910 =
                                      let uu____10917 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10917)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10910  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___249_10933  ->
                                         match uu___249_10933 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10934,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10936;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10937;_})
                                             ->
                                             let uu____10942 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10942
                                         | uu____10943 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10944 -> subst1)) env []
  
let reduce_primops :
  'Auu____10967 'Auu____10968 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10967) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10968 ->
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
            (let uu____11016 = FStar_Syntax_Util.head_and_args tm  in
             match uu____11016 with
             | (head1,args) ->
                 let uu____11061 =
                   let uu____11062 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11062.FStar_Syntax_Syntax.n  in
                 (match uu____11061 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____11068 = find_prim_step cfg fv  in
                      (match uu____11068 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____11096  ->
                                   let uu____11097 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____11098 =
                                     FStar_Util.string_of_int l  in
                                   let uu____11105 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____11097 uu____11098 uu____11105);
                              tm)
                           else
                             (let uu____11107 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____11107 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____11244  ->
                                        let uu____11245 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____11245);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____11248  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____11250 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____11250 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____11258  ->
                                              let uu____11259 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____11259);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____11265  ->
                                              let uu____11266 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____11267 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____11266 uu____11267);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____11268 ->
                           (log_primops cfg
                              (fun uu____11272  ->
                                 let uu____11273 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____11273);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11277  ->
                            let uu____11278 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11278);
                       (match args with
                        | (a1,uu____11282)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____11307 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____11321  ->
                            let uu____11322 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____11322);
                       (match args with
                        | (t,uu____11326)::(r,uu____11328)::[] ->
                            let uu____11369 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____11369 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____11375 -> tm))
                  | uu____11386 -> tm))
  
let reduce_equality :
  'Auu____11397 'Auu____11398 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____11397) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____11398 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___310_11444 = cfg  in
         {
           steps =
             (let uu___311_11447 = default_steps  in
              {
                beta = (uu___311_11447.beta);
                iota = (uu___311_11447.iota);
                zeta = (uu___311_11447.zeta);
                weak = (uu___311_11447.weak);
                hnf = (uu___311_11447.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___311_11447.do_not_unfold_pure_lets);
                unfold_until = (uu___311_11447.unfold_until);
                unfold_only = (uu___311_11447.unfold_only);
                unfold_fully = (uu___311_11447.unfold_fully);
                unfold_attr = (uu___311_11447.unfold_attr);
                unfold_tac = (uu___311_11447.unfold_tac);
                pure_subterms_within_computations =
                  (uu___311_11447.pure_subterms_within_computations);
                simplify = (uu___311_11447.simplify);
                erase_universes = (uu___311_11447.erase_universes);
                allow_unbound_universes =
                  (uu___311_11447.allow_unbound_universes);
                reify_ = (uu___311_11447.reify_);
                compress_uvars = (uu___311_11447.compress_uvars);
                no_full_norm = (uu___311_11447.no_full_norm);
                check_no_uvars = (uu___311_11447.check_no_uvars);
                unmeta = (uu___311_11447.unmeta);
                unascribe = (uu___311_11447.unascribe);
                in_full_norm_request = (uu___311_11447.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___311_11447.weakly_reduce_scrutinee)
              });
           tcenv = (uu___310_11444.tcenv);
           debug = (uu___310_11444.debug);
           delta_level = (uu___310_11444.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___310_11444.strong);
           memoize_lazy = (uu___310_11444.memoize_lazy);
           normalize_pure_lets = (uu___310_11444.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11454 .
    FStar_Syntax_Syntax.term -> 'Auu____11454 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11469 =
        let uu____11476 =
          let uu____11477 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11477.FStar_Syntax_Syntax.n  in
        (uu____11476, args)  in
      match uu____11469 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11483::uu____11484::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11488::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11493::uu____11494::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11497 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___250_11510  ->
    match uu___250_11510 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11516 =
          let uu____11519 =
            let uu____11520 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11520  in
          [uu____11519]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11516
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11526 =
          let uu____11529 =
            let uu____11530 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11530  in
          [uu____11529]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11526
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11553 .
    cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____11553)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11604 =
            let uu____11609 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____11609 s  in
          match uu____11604 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11625 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11625
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if (cfg.steps).erase_universes then [EraseUniverses] else [])
            (if (cfg.steps).allow_unbound_universes
             then [AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____11651::(tm,uu____11653)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____11682)::[] ->
            let s =
              [Beta;
              Zeta;
              Iota;
              Primops;
              UnfoldUntil FStar_Syntax_Syntax.delta_constant;
              Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____11703)::uu____11704::(tm,uu____11706)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s then s else (Exclude z) :: s  in
            let uu____11747 =
              let uu____11752 = full_norm steps  in parse_steps uu____11752
               in
            (match uu____11747 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = Beta :: s  in
                 let s2 = add_exclude s1 Zeta  in
                 let s3 = add_exclude s2 Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____11791 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___251_11810  ->
    match uu___251_11810 with
    | (App
        (uu____11813,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11814;
                       FStar_Syntax_Syntax.vars = uu____11815;_},uu____11816,uu____11817))::uu____11818
        -> true
    | uu____11823 -> false
  
let firstn :
  'Auu____11832 .
    Prims.int ->
      'Auu____11832 Prims.list ->
        ('Auu____11832 Prims.list,'Auu____11832 Prims.list)
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
          (uu____11874,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11875;
                         FStar_Syntax_Syntax.vars = uu____11876;_},uu____11877,uu____11878))::uu____11879
          -> (cfg.steps).reify_
      | uu____11884 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11907) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11917) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11938  ->
                  match uu____11938 with
                  | (a,uu____11948) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11958 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11981 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11982 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11995 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11996 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11997 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11998 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11999 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____12000 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____12007 -> false
    | FStar_Syntax_Syntax.Tm_let uu____12014 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____12027 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____12046 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____12061 -> true
    | FStar_Syntax_Syntax.Tm_match uu____12068 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____12138  ->
                   match uu____12138 with
                   | (a,uu____12148) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____12159) ->
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
                     (fun uu____12287  ->
                        match uu____12287 with
                        | (a,uu____12297) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____12306,uu____12307,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____12313,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____12319 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____12326 -> false
            | FStar_Syntax_Syntax.Meta_named uu____12327 -> false))
  
let decide_unfolding :
  'Auu____12342 .
    cfg ->
      'Auu____12342 Prims.list ->
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
                (fun uu____12434  ->
                   let uu____12435 = FStar_Syntax_Print.fv_to_string fv  in
                   let uu____12436 =
                     FStar_Util.string_of_int (FStar_List.length env)  in
                   let uu____12437 =
                     let uu____12438 =
                       let uu____12441 = firstn (Prims.parse_int "4") stack
                          in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____12441
                        in
                     stack_to_string uu____12438  in
                   FStar_Util.print3
                     ">>> Deciding unfolding of %s with %s env elements top of the stack %s \n"
                     uu____12435 uu____12436 uu____12437);
              (let attrs =
                 let uu____12467 =
                   FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                 match uu____12467 with
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
                   (fun uu____12595  ->
                      fun uu____12596  ->
                        match (uu____12595, uu____12596) with
                        | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z)))
                   l (false, false, false)
                  in
               let string_of_res uu____12656 =
                 match uu____12656 with
                 | (x,y,z) ->
                     let uu____12666 = FStar_Util.string_of_bool x  in
                     let uu____12667 = FStar_Util.string_of_bool y  in
                     let uu____12668 = FStar_Util.string_of_bool z  in
                     FStar_Util.format3 "(%s,%s,%s)" uu____12666 uu____12667
                       uu____12668
                  in
               let res =
                 match (qninfo, ((cfg.steps).unfold_only),
                         ((cfg.steps).unfold_fully),
                         ((cfg.steps).unfold_attr))
                 with
                 | uu____12714 when
                     FStar_TypeChecker_Env.qninfo_is_action qninfo ->
                     let b = should_reify cfg stack  in
                     (log_unfolding cfg
                        (fun uu____12760  ->
                           let uu____12761 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____12762 = FStar_Util.string_of_bool b  in
                           FStar_Util.print2
                             " >> For DM4F action %s, should_reify = %s\n"
                             uu____12761 uu____12762);
                      if b then reif else no)
                 | uu____12770 when
                     let uu____12811 = find_prim_step cfg fv  in
                     FStar_Option.isSome uu____12811 -> no
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____12815),uu____12816);
                        FStar_Syntax_Syntax.sigrng = uu____12817;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____12819;
                        FStar_Syntax_Syntax.sigattrs = uu____12820;_},uu____12821),uu____12822),uu____12823,uu____12824,uu____12825)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     -> no
                 | (uu____12928,uu____12929,uu____12930,uu____12931) when
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
                          ((is_rec,uu____12997),uu____12998);
                        FStar_Syntax_Syntax.sigrng = uu____12999;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____13001;
                        FStar_Syntax_Syntax.sigattrs = uu____13002;_},uu____13003),uu____13004),uu____13005,uu____13006,uu____13007)
                     when is_rec && (Prims.op_Negation (cfg.steps).zeta) ->
                     no
                 | (uu____13110,FStar_Pervasives_Native.Some
                    uu____13111,uu____13112,uu____13113) ->
                     (log_unfolding cfg
                        (fun uu____13181  ->
                           let uu____13182 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13182);
                      (let uu____13183 =
                         let uu____13192 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13212 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13212
                            in
                         let uu____13219 =
                           let uu____13228 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13248 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13248
                              in
                           let uu____13257 =
                             let uu____13266 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13286 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13286
                                in
                             [uu____13266]  in
                           uu____13228 :: uu____13257  in
                         uu____13192 :: uu____13219  in
                       comb_or uu____13183))
                 | (uu____13317,uu____13318,FStar_Pervasives_Native.Some
                    uu____13319,uu____13320) ->
                     (log_unfolding cfg
                        (fun uu____13388  ->
                           let uu____13389 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13389);
                      (let uu____13390 =
                         let uu____13399 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13419 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13419
                            in
                         let uu____13426 =
                           let uu____13435 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13455 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13455
                              in
                           let uu____13464 =
                             let uu____13473 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13493 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13493
                                in
                             [uu____13473]  in
                           uu____13435 :: uu____13464  in
                         uu____13399 :: uu____13426  in
                       comb_or uu____13390))
                 | (uu____13524,uu____13525,uu____13526,FStar_Pervasives_Native.Some
                    uu____13527) ->
                     (log_unfolding cfg
                        (fun uu____13595  ->
                           let uu____13596 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             " >> Reached a %s with selective unfolding\n"
                             uu____13596);
                      (let uu____13597 =
                         let uu____13606 =
                           match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____13626 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____13626
                            in
                         let uu____13633 =
                           let uu____13642 =
                             match (cfg.steps).unfold_attr with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____13662 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____13662
                              in
                           let uu____13671 =
                             let uu____13680 =
                               match (cfg.steps).unfold_fully with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____13700 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____13700
                                in
                             [uu____13680]  in
                           uu____13642 :: uu____13671  in
                         uu____13606 :: uu____13633  in
                       comb_or uu____13597))
                 | uu____13731 ->
                     (log_unfolding cfg
                        (fun uu____13777  ->
                           let uu____13778 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____13779 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____13780 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.delta_level
                              in
                           FStar_Util.print3
                             " >> Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____13778 uu____13779 uu____13780);
                      (let uu____13781 =
                         FStar_All.pipe_right cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___252_13785  ->
                                 match uu___252_13785 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.Inlining  -> true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____13781))
                  in
               log_unfolding cfg
                 (fun uu____13798  ->
                    let uu____13799 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____13800 = FStar_Range.string_of_range rng  in
                    let uu____13801 = string_of_res res  in
                    FStar_Util.print3 " >> For %s (%s), unfolding res = %s\n"
                      uu____13799 uu____13800 uu____13801);
               (match res with
                | (false ,uu____13810,uu____13811) ->
                    FStar_Pervasives_Native.None
                | (true ,false ,false ) ->
                    FStar_Pervasives_Native.Some (cfg, stack)
                | (true ,true ,false ) ->
                    let cfg' =
                      let uu___312_13827 = cfg  in
                      {
                        steps =
                          (let uu___313_13830 = cfg.steps  in
                           {
                             beta = (uu___313_13830.beta);
                             iota = (uu___313_13830.iota);
                             zeta = (uu___313_13830.zeta);
                             weak = (uu___313_13830.weak);
                             hnf = (uu___313_13830.hnf);
                             primops = (uu___313_13830.primops);
                             do_not_unfold_pure_lets =
                               (uu___313_13830.do_not_unfold_pure_lets);
                             unfold_until =
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.delta_constant);
                             unfold_only = FStar_Pervasives_Native.None;
                             unfold_fully = FStar_Pervasives_Native.None;
                             unfold_attr = FStar_Pervasives_Native.None;
                             unfold_tac = (uu___313_13830.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___313_13830.pure_subterms_within_computations);
                             simplify = (uu___313_13830.simplify);
                             erase_universes =
                               (uu___313_13830.erase_universes);
                             allow_unbound_universes =
                               (uu___313_13830.allow_unbound_universes);
                             reify_ = (uu___313_13830.reify_);
                             compress_uvars = (uu___313_13830.compress_uvars);
                             no_full_norm = (uu___313_13830.no_full_norm);
                             check_no_uvars = (uu___313_13830.check_no_uvars);
                             unmeta = (uu___313_13830.unmeta);
                             unascribe = (uu___313_13830.unascribe);
                             in_full_norm_request =
                               (uu___313_13830.in_full_norm_request);
                             weakly_reduce_scrutinee =
                               (uu___313_13830.weakly_reduce_scrutinee)
                           });
                        tcenv = (uu___312_13827.tcenv);
                        debug = (uu___312_13827.debug);
                        delta_level = (uu___312_13827.delta_level);
                        primitive_steps = (uu___312_13827.primitive_steps);
                        strong = (uu___312_13827.strong);
                        memoize_lazy = (uu___312_13827.memoize_lazy);
                        normalize_pure_lets =
                          (uu___312_13827.normalize_pure_lets)
                      }  in
                    let stack' = (Cfg cfg) :: stack  in
                    FStar_Pervasives_Native.Some (cfg', stack')
                | (true ,false ,true ) ->
                    let uu____13848 =
                      let uu____13855 = FStar_List.tl stack  in
                      (cfg, uu____13855)  in
                    FStar_Pervasives_Native.Some uu____13848
                | uu____13866 ->
                    let uu____13873 =
                      let uu____13874 = string_of_res res  in
                      FStar_Util.format1 "Unexpected unfolding result: %s"
                        uu____13874
                       in
                    FStar_All.pipe_left failwith uu____13873))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____14190 ->
                   let uu____14213 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____14213
               | uu____14214 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____14222  ->
               let uu____14223 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____14224 = FStar_Syntax_Print.term_to_string t1  in
               let uu____14225 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____14232 =
                 let uu____14233 =
                   let uu____14236 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____14236
                    in
                 stack_to_string uu____14233  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____14223 uu____14224 uu____14225 uu____14232);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (log_unfolding cfg
                  (fun uu____14262  ->
                     let uu____14263 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14263);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____14264 ->
               (log_unfolding cfg
                  (fun uu____14268  ->
                     let uu____14269 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14269);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____14270 ->
               (log_unfolding cfg
                  (fun uu____14274  ->
                     let uu____14275 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14275);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____14276 ->
               (log_unfolding cfg
                  (fun uu____14280  ->
                     let uu____14281 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14281);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14282;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____14283;_}
               when _0_17 = (Prims.parse_int "0") ->
               (log_unfolding cfg
                  (fun uu____14289  ->
                     let uu____14290 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14290);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14291;
                 FStar_Syntax_Syntax.fv_delta = uu____14292;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (log_unfolding cfg
                  (fun uu____14296  ->
                     let uu____14297 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14297);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____14298;
                 FStar_Syntax_Syntax.fv_delta = uu____14299;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____14300);_}
               ->
               (log_unfolding cfg
                  (fun uu____14310  ->
                     let uu____14311 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____14311);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14314 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14314  in
               let uu____14315 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____14315 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____14348 ->
               let uu____14355 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14355
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____14391 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____14391)
               ->
               let cfg' =
                 let uu___314_14393 = cfg  in
                 {
                   steps =
                     (let uu___315_14396 = cfg.steps  in
                      {
                        beta = (uu___315_14396.beta);
                        iota = (uu___315_14396.iota);
                        zeta = (uu___315_14396.zeta);
                        weak = (uu___315_14396.weak);
                        hnf = (uu___315_14396.hnf);
                        primops = (uu___315_14396.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___315_14396.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___315_14396.unfold_attr);
                        unfold_tac = (uu___315_14396.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___315_14396.pure_subterms_within_computations);
                        simplify = (uu___315_14396.simplify);
                        erase_universes = (uu___315_14396.erase_universes);
                        allow_unbound_universes =
                          (uu___315_14396.allow_unbound_universes);
                        reify_ = (uu___315_14396.reify_);
                        compress_uvars = (uu___315_14396.compress_uvars);
                        no_full_norm = (uu___315_14396.no_full_norm);
                        check_no_uvars = (uu___315_14396.check_no_uvars);
                        unmeta = (uu___315_14396.unmeta);
                        unascribe = (uu___315_14396.unascribe);
                        in_full_norm_request =
                          (uu___315_14396.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___315_14396.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___314_14393.tcenv);
                   debug = (uu___314_14393.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___314_14393.primitive_steps);
                   strong = (uu___314_14393.strong);
                   memoize_lazy = (uu___314_14393.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____14401 = get_norm_request cfg (norm cfg' env []) args
                  in
               (match uu____14401 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14432  ->
                              fun stack1  ->
                                match uu____14432 with
                                | (a,aq) ->
                                    let uu____14444 =
                                      let uu____14445 =
                                        let uu____14452 =
                                          let uu____14453 =
                                            let uu____14484 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14484, false)  in
                                          Clos uu____14453  in
                                        (uu____14452, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14445  in
                                    uu____14444 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14572  ->
                          let uu____14573 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14573);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14597 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___253_14602  ->
                                match uu___253_14602 with
                                | UnfoldUntil uu____14603 -> true
                                | UnfoldOnly uu____14604 -> true
                                | UnfoldFully uu____14607 -> true
                                | uu____14610 -> false))
                         in
                      if uu____14597
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___316_14615 = cfg  in
                      let uu____14616 =
                        let uu___317_14617 = to_fsteps s  in
                        {
                          beta = (uu___317_14617.beta);
                          iota = (uu___317_14617.iota);
                          zeta = (uu___317_14617.zeta);
                          weak = (uu___317_14617.weak);
                          hnf = (uu___317_14617.hnf);
                          primops = (uu___317_14617.primops);
                          do_not_unfold_pure_lets =
                            (uu___317_14617.do_not_unfold_pure_lets);
                          unfold_until = (uu___317_14617.unfold_until);
                          unfold_only = (uu___317_14617.unfold_only);
                          unfold_fully = (uu___317_14617.unfold_fully);
                          unfold_attr = (uu___317_14617.unfold_attr);
                          unfold_tac = (uu___317_14617.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___317_14617.pure_subterms_within_computations);
                          simplify = (uu___317_14617.simplify);
                          erase_universes = (uu___317_14617.erase_universes);
                          allow_unbound_universes =
                            (uu___317_14617.allow_unbound_universes);
                          reify_ = (uu___317_14617.reify_);
                          compress_uvars = (uu___317_14617.compress_uvars);
                          no_full_norm = (uu___317_14617.no_full_norm);
                          check_no_uvars = (uu___317_14617.check_no_uvars);
                          unmeta = (uu___317_14617.unmeta);
                          unascribe = (uu___317_14617.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___317_14617.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____14616;
                        tcenv = (uu___316_14615.tcenv);
                        debug = (uu___316_14615.debug);
                        delta_level;
                        primitive_steps = (uu___316_14615.primitive_steps);
                        strong = (uu___316_14615.strong);
                        memoize_lazy = (uu___316_14615.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14622 =
                          let uu____14623 =
                            let uu____14628 = FStar_Util.now ()  in
                            (t1, uu____14628)  in
                          Debug uu____14623  in
                        uu____14622 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14632 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14632
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14641 =
                      let uu____14648 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14648, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14641  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14657 = lookup_bvar env x  in
               (match uu____14657 with
                | Univ uu____14658 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14707 = FStar_ST.op_Bang r  in
                      (match uu____14707 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14825  ->
                                 let uu____14826 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14827 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14826
                                   uu____14827);
                            (let uu____14828 = maybe_weakly_reduced t'  in
                             if uu____14828
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____14829 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14904)::uu____14905 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____14915,uu____14916))::stack_rest ->
                    (match c with
                     | Univ uu____14920 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14929 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14958  ->
                                    let uu____14959 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14959);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14993  ->
                                    let uu____14994 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14994);
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
                       (fun uu____15062  ->
                          let uu____15063 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____15063);
                     norm cfg env stack1 t1)
                | (Match uu____15064)::uu____15065 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___318_15079 = cfg.steps  in
                             {
                               beta = (uu___318_15079.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15079.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15079.unfold_until);
                               unfold_only = (uu___318_15079.unfold_only);
                               unfold_fully = (uu___318_15079.unfold_fully);
                               unfold_attr = (uu___318_15079.unfold_attr);
                               unfold_tac = (uu___318_15079.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15079.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15079.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15079.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15079.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15079.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15079.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15081 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15081.tcenv);
                               debug = (uu___319_15081.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15081.primitive_steps);
                               strong = (uu___319_15081.strong);
                               memoize_lazy = (uu___319_15081.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15081.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15083 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15083 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15119  -> dummy :: env1) env)
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
                                          let uu____15162 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15162)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15169 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15169.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15169.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15170 -> lopt  in
                           (log cfg
                              (fun uu____15176  ->
                                 let uu____15177 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15177);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15188 = cfg  in
                               {
                                 steps = (uu___321_15188.steps);
                                 tcenv = (uu___321_15188.tcenv);
                                 debug = (uu___321_15188.debug);
                                 delta_level = (uu___321_15188.delta_level);
                                 primitive_steps =
                                   (uu___321_15188.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15188.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15188.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____15191)::uu____15192 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___318_15202 = cfg.steps  in
                             {
                               beta = (uu___318_15202.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15202.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15202.unfold_until);
                               unfold_only = (uu___318_15202.unfold_only);
                               unfold_fully = (uu___318_15202.unfold_fully);
                               unfold_attr = (uu___318_15202.unfold_attr);
                               unfold_tac = (uu___318_15202.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15202.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15202.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15202.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15202.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15202.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15202.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15204 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15204.tcenv);
                               debug = (uu___319_15204.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15204.primitive_steps);
                               strong = (uu___319_15204.strong);
                               memoize_lazy = (uu___319_15204.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15204.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15206 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15206 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15242  -> dummy :: env1) env)
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
                                          let uu____15285 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15285)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15292 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15292.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15292.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15293 -> lopt  in
                           (log cfg
                              (fun uu____15299  ->
                                 let uu____15300 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15300);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15311 = cfg  in
                               {
                                 steps = (uu___321_15311.steps);
                                 tcenv = (uu___321_15311.tcenv);
                                 debug = (uu___321_15311.debug);
                                 delta_level = (uu___321_15311.delta_level);
                                 primitive_steps =
                                   (uu___321_15311.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15311.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15311.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____15314)::uu____15315 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___318_15327 = cfg.steps  in
                             {
                               beta = (uu___318_15327.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15327.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15327.unfold_until);
                               unfold_only = (uu___318_15327.unfold_only);
                               unfold_fully = (uu___318_15327.unfold_fully);
                               unfold_attr = (uu___318_15327.unfold_attr);
                               unfold_tac = (uu___318_15327.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15327.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15327.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15327.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15327.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15327.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15327.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15329 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15329.tcenv);
                               debug = (uu___319_15329.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15329.primitive_steps);
                               strong = (uu___319_15329.strong);
                               memoize_lazy = (uu___319_15329.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15329.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15331 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15331 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15367  -> dummy :: env1) env)
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
                                          let uu____15410 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15410)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15417 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15417.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15417.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15418 -> lopt  in
                           (log cfg
                              (fun uu____15424  ->
                                 let uu____15425 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15425);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15436 = cfg  in
                               {
                                 steps = (uu___321_15436.steps);
                                 tcenv = (uu___321_15436.tcenv);
                                 debug = (uu___321_15436.debug);
                                 delta_level = (uu___321_15436.delta_level);
                                 primitive_steps =
                                   (uu___321_15436.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15436.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15436.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____15439)::uu____15440 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___318_15454 = cfg.steps  in
                             {
                               beta = (uu___318_15454.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15454.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15454.unfold_until);
                               unfold_only = (uu___318_15454.unfold_only);
                               unfold_fully = (uu___318_15454.unfold_fully);
                               unfold_attr = (uu___318_15454.unfold_attr);
                               unfold_tac = (uu___318_15454.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15454.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15454.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15454.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15454.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15454.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15454.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15456 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15456.tcenv);
                               debug = (uu___319_15456.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15456.primitive_steps);
                               strong = (uu___319_15456.strong);
                               memoize_lazy = (uu___319_15456.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15456.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15458 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15458 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15494  -> dummy :: env1) env)
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
                                          let uu____15537 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15537)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15544 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15544.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15544.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15545 -> lopt  in
                           (log cfg
                              (fun uu____15551  ->
                                 let uu____15552 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15552);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15563 = cfg  in
                               {
                                 steps = (uu___321_15563.steps);
                                 tcenv = (uu___321_15563.tcenv);
                                 debug = (uu___321_15563.debug);
                                 delta_level = (uu___321_15563.delta_level);
                                 primitive_steps =
                                   (uu___321_15563.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15563.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15563.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15566)::uu____15567 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___318_15581 = cfg.steps  in
                             {
                               beta = (uu___318_15581.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15581.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15581.unfold_until);
                               unfold_only = (uu___318_15581.unfold_only);
                               unfold_fully = (uu___318_15581.unfold_fully);
                               unfold_attr = (uu___318_15581.unfold_attr);
                               unfold_tac = (uu___318_15581.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15581.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15581.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15581.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15581.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15581.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15581.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15583 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15583.tcenv);
                               debug = (uu___319_15583.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15583.primitive_steps);
                               strong = (uu___319_15583.strong);
                               memoize_lazy = (uu___319_15583.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15583.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15585 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15585 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15621  -> dummy :: env1) env)
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
                                          let uu____15664 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15664)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15671 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15671.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15671.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15672 -> lopt  in
                           (log cfg
                              (fun uu____15678  ->
                                 let uu____15679 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15679);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15690 = cfg  in
                               {
                                 steps = (uu___321_15690.steps);
                                 tcenv = (uu___321_15690.tcenv);
                                 debug = (uu___321_15690.debug);
                                 delta_level = (uu___321_15690.delta_level);
                                 primitive_steps =
                                   (uu___321_15690.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15690.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15690.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15693)::uu____15694 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___318_15712 = cfg.steps  in
                             {
                               beta = (uu___318_15712.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15712.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15712.unfold_until);
                               unfold_only = (uu___318_15712.unfold_only);
                               unfold_fully = (uu___318_15712.unfold_fully);
                               unfold_attr = (uu___318_15712.unfold_attr);
                               unfold_tac = (uu___318_15712.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15712.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15712.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15712.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15712.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15712.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15712.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15714 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15714.tcenv);
                               debug = (uu___319_15714.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15714.primitive_steps);
                               strong = (uu___319_15714.strong);
                               memoize_lazy = (uu___319_15714.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15714.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15716 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15716 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15752  -> dummy :: env1) env)
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
                                          let uu____15795 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15795)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15802 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15802.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15802.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15803 -> lopt  in
                           (log cfg
                              (fun uu____15809  ->
                                 let uu____15810 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15810);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15821 = cfg  in
                               {
                                 steps = (uu___321_15821.steps);
                                 tcenv = (uu___321_15821.tcenv);
                                 debug = (uu___321_15821.debug);
                                 delta_level = (uu___321_15821.delta_level);
                                 primitive_steps =
                                   (uu___321_15821.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15821.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15821.normalize_pure_lets)
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
                             let uu___318_15827 = cfg.steps  in
                             {
                               beta = (uu___318_15827.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___318_15827.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___318_15827.unfold_until);
                               unfold_only = (uu___318_15827.unfold_only);
                               unfold_fully = (uu___318_15827.unfold_fully);
                               unfold_attr = (uu___318_15827.unfold_attr);
                               unfold_tac = (uu___318_15827.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___318_15827.erase_universes);
                               allow_unbound_universes =
                                 (uu___318_15827.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___318_15827.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___318_15827.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___318_15827.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___318_15827.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___319_15829 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___319_15829.tcenv);
                               debug = (uu___319_15829.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___319_15829.primitive_steps);
                               strong = (uu___319_15829.strong);
                               memoize_lazy = (uu___319_15829.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___319_15829.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____15831 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15831 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15867  -> dummy :: env1) env)
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
                                          let uu____15910 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15910)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___320_15917 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___320_15917.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___320_15917.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15918 -> lopt  in
                           (log cfg
                              (fun uu____15924  ->
                                 let uu____15925 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15925);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___321_15936 = cfg  in
                               {
                                 steps = (uu___321_15936.steps);
                                 tcenv = (uu___321_15936.tcenv);
                                 debug = (uu___321_15936.debug);
                                 delta_level = (uu___321_15936.delta_level);
                                 primitive_steps =
                                   (uu___321_15936.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___321_15936.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___321_15936.normalize_pure_lets)
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
                      (fun uu____15979  ->
                         fun stack1  ->
                           match uu____15979 with
                           | (a,aq) ->
                               let uu____15991 =
                                 let uu____15992 =
                                   let uu____15999 =
                                     let uu____16000 =
                                       let uu____16031 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____16031, false)  in
                                     Clos uu____16000  in
                                   (uu____15999, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15992  in
                               uu____15991 :: stack1) args)
                  in
               (log cfg
                  (fun uu____16119  ->
                     let uu____16120 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____16120);
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
                             ((let uu___322_16168 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___322_16168.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___322_16168.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____16169 ->
                      let uu____16184 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____16184)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____16187 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____16187 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____16218 =
                          let uu____16219 =
                            let uu____16226 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___323_16232 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___323_16232.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___323_16232.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____16226)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____16219  in
                        mk uu____16218 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____16255 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____16255
               else
                 (let uu____16257 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____16257 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____16265 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____16291  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____16265 c1  in
                      let t2 =
                        let uu____16315 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____16315 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____16428)::uu____16429 ->
                    (log cfg
                       (fun uu____16442  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____16443)::uu____16444 ->
                    (log cfg
                       (fun uu____16455  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____16456,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____16457;
                                   FStar_Syntax_Syntax.vars = uu____16458;_},uu____16459,uu____16460))::uu____16461
                    ->
                    (log cfg
                       (fun uu____16468  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____16469)::uu____16470 ->
                    (log cfg
                       (fun uu____16481  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____16482 ->
                    (log cfg
                       (fun uu____16485  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____16489  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____16514 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____16514
                         | FStar_Util.Inr c ->
                             let uu____16528 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16528
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16551 =
                               let uu____16552 =
                                 let uu____16579 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16579, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16552
                                in
                             mk uu____16551 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16614 ->
                           let uu____16615 =
                             let uu____16616 =
                               let uu____16617 =
                                 let uu____16644 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16644, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16617
                                in
                             mk uu____16616 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16615))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee) &&
                   (Prims.op_Negation (cfg.steps).weak)
               then
                 let cfg' =
                   let uu___324_16721 = cfg  in
                   {
                     steps =
                       (let uu___325_16724 = cfg.steps  in
                        {
                          beta = (uu___325_16724.beta);
                          iota = (uu___325_16724.iota);
                          zeta = (uu___325_16724.zeta);
                          weak = true;
                          hnf = (uu___325_16724.hnf);
                          primops = (uu___325_16724.primops);
                          do_not_unfold_pure_lets =
                            (uu___325_16724.do_not_unfold_pure_lets);
                          unfold_until = (uu___325_16724.unfold_until);
                          unfold_only = (uu___325_16724.unfold_only);
                          unfold_fully = (uu___325_16724.unfold_fully);
                          unfold_attr = (uu___325_16724.unfold_attr);
                          unfold_tac = (uu___325_16724.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___325_16724.pure_subterms_within_computations);
                          simplify = (uu___325_16724.simplify);
                          erase_universes = (uu___325_16724.erase_universes);
                          allow_unbound_universes =
                            (uu___325_16724.allow_unbound_universes);
                          reify_ = (uu___325_16724.reify_);
                          compress_uvars = (uu___325_16724.compress_uvars);
                          no_full_norm = (uu___325_16724.no_full_norm);
                          check_no_uvars = (uu___325_16724.check_no_uvars);
                          unmeta = (uu___325_16724.unmeta);
                          unascribe = (uu___325_16724.unascribe);
                          in_full_norm_request =
                            (uu___325_16724.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___325_16724.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___324_16721.tcenv);
                     debug = (uu___324_16721.debug);
                     delta_level = (uu___324_16721.delta_level);
                     primitive_steps = (uu___324_16721.primitive_steps);
                     strong = (uu___324_16721.strong);
                     memoize_lazy = (uu___324_16721.memoize_lazy);
                     normalize_pure_lets =
                       (uu___324_16721.normalize_pure_lets)
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
                         let uu____16760 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16760 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___326_16780 = cfg  in
                               let uu____16781 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___326_16780.steps);
                                 tcenv = uu____16781;
                                 debug = (uu___326_16780.debug);
                                 delta_level = (uu___326_16780.delta_level);
                                 primitive_steps =
                                   (uu___326_16780.primitive_steps);
                                 strong = (uu___326_16780.strong);
                                 memoize_lazy = (uu___326_16780.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___326_16780.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16788 =
                                 let uu____16789 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16789  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16788
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___327_16792 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___327_16792.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___327_16792.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___327_16792.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___327_16792.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16793 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16793
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16804,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16805;
                               FStar_Syntax_Syntax.lbunivs = uu____16806;
                               FStar_Syntax_Syntax.lbtyp = uu____16807;
                               FStar_Syntax_Syntax.lbeff = uu____16808;
                               FStar_Syntax_Syntax.lbdef = uu____16809;
                               FStar_Syntax_Syntax.lbattrs = uu____16810;
                               FStar_Syntax_Syntax.lbpos = uu____16811;_}::uu____16812),uu____16813)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16853 =
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
               if uu____16853
               then
                 let binder =
                   let uu____16855 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16855  in
                 let env1 =
                   let uu____16865 =
                     let uu____16872 =
                       let uu____16873 =
                         let uu____16904 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16904,
                           false)
                          in
                       Clos uu____16873  in
                     ((FStar_Pervasives_Native.Some binder), uu____16872)  in
                   uu____16865 :: env  in
                 (log cfg
                    (fun uu____16999  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____17003  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____17004 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____17004))
                 else
                   (let uu____17006 =
                      let uu____17011 =
                        let uu____17012 =
                          let uu____17019 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____17019
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____17012]  in
                      FStar_Syntax_Subst.open_term uu____17011 body  in
                    match uu____17006 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____17046  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____17054 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____17054  in
                            FStar_Util.Inl
                              (let uu___328_17070 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___328_17070.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___328_17070.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____17073  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___329_17075 = lb  in
                             let uu____17076 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___329_17075.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___329_17075.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____17076;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___329_17075.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___329_17075.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____17105  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___330_17130 = cfg  in
                             {
                               steps = (uu___330_17130.steps);
                               tcenv = (uu___330_17130.tcenv);
                               debug = (uu___330_17130.debug);
                               delta_level = (uu___330_17130.delta_level);
                               primitive_steps =
                                 (uu___330_17130.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___330_17130.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___330_17130.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____17133  ->
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
               let uu____17150 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____17150 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____17186 =
                               let uu___331_17187 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___331_17187.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___331_17187.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____17186  in
                           let uu____17188 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____17188 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____17214 =
                                   FStar_List.map (fun uu____17230  -> dummy)
                                     lbs1
                                    in
                                 let uu____17231 =
                                   let uu____17240 =
                                     FStar_List.map
                                       (fun uu____17262  -> dummy) xs1
                                      in
                                   FStar_List.append uu____17240 env  in
                                 FStar_List.append uu____17214 uu____17231
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____17288 =
                                       let uu___332_17289 = rc  in
                                       let uu____17290 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___332_17289.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____17290;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___332_17289.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____17288
                                 | uu____17299 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___333_17305 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___333_17305.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___333_17305.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___333_17305.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___333_17305.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____17315 =
                        FStar_List.map (fun uu____17331  -> dummy) lbs2  in
                      FStar_List.append uu____17315 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____17339 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____17339 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___334_17355 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___334_17355.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___334_17355.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____17384 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____17384
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____17403 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____17479  ->
                        match uu____17479 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___335_17600 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___335_17600.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___335_17600.FStar_Syntax_Syntax.sort)
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
               (match uu____17403 with
                | (rec_env,memos,uu____17827) ->
                    let uu____17880 =
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
                             let uu____18191 =
                               let uu____18198 =
                                 let uu____18199 =
                                   let uu____18230 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____18230, false)
                                    in
                                 Clos uu____18199  in
                               (FStar_Pervasives_Native.None, uu____18198)
                                in
                             uu____18191 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____18334  ->
                     let uu____18335 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____18335);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____18357 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____18359::uu____18360 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____18365) ->
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
                             | uu____18392 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____18408 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____18408
                              | uu____18421 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____18427 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____18451 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____18465 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____18478 =
                        let uu____18479 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____18480 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____18479 uu____18480
                         in
                      failwith uu____18478
                    else
                      (let uu____18482 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____18482)
                | uu____18483 -> norm cfg env stack t2))

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
              let uu____18492 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____18492 with
              | FStar_Pervasives_Native.None  ->
                  (log_unfolding cfg
                     (fun uu____18506  ->
                        let uu____18507 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____18507);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log_unfolding cfg
                     (fun uu____18518  ->
                        let uu____18519 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____18520 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____18519 uu____18520);
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
                      | (UnivArgs (us',uu____18533))::stack1 ->
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
                      | uu____18572 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____18575 ->
                          let uu____18578 =
                            let uu____18579 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____18579
                             in
                          failwith uu____18578
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
                  let uu___336_18603 = cfg  in
                  let uu____18604 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18604;
                    tcenv = (uu___336_18603.tcenv);
                    debug = (uu___336_18603.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___336_18603.primitive_steps);
                    strong = (uu___336_18603.strong);
                    memoize_lazy = (uu___336_18603.memoize_lazy);
                    normalize_pure_lets =
                      (uu___336_18603.normalize_pure_lets)
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
                  (fun uu____18639  ->
                     let uu____18640 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18641 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18640
                       uu____18641);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18643 =
                   let uu____18644 = FStar_Syntax_Subst.compress head3  in
                   uu____18644.FStar_Syntax_Syntax.n  in
                 match uu____18643 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18662 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18662
                        in
                     let uu____18663 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18663 with
                      | (uu____18664,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18674 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18684 =
                                   let uu____18685 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18685.FStar_Syntax_Syntax.n  in
                                 match uu____18684 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18691,uu____18692))
                                     ->
                                     let uu____18701 =
                                       let uu____18702 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18702.FStar_Syntax_Syntax.n  in
                                     (match uu____18701 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18708,msrc,uu____18710))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18719 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18719
                                      | uu____18720 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18721 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18722 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18722 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___337_18727 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___337_18727.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___337_18727.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___337_18727.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___337_18727.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___337_18727.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18728 = FStar_List.tl stack  in
                                    let uu____18729 =
                                      let uu____18730 =
                                        let uu____18737 =
                                          let uu____18738 =
                                            let uu____18751 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18751)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18738
                                           in
                                        FStar_Syntax_Syntax.mk uu____18737
                                         in
                                      uu____18730
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18728 uu____18729
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18767 =
                                      let uu____18768 = is_return body  in
                                      match uu____18768 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18772;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18773;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18776 -> false  in
                                    if uu____18767
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
                                         let uu____18797 =
                                           let uu____18804 =
                                             let uu____18805 =
                                               let uu____18824 =
                                                 let uu____18833 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18833]  in
                                               (uu____18824, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18805
                                              in
                                           FStar_Syntax_Syntax.mk uu____18804
                                            in
                                         uu____18797
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18875 =
                                           let uu____18876 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18876.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18875 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18882::uu____18883::[])
                                             ->
                                             let uu____18888 =
                                               let uu____18895 =
                                                 let uu____18896 =
                                                   let uu____18903 =
                                                     let uu____18904 =
                                                       let uu____18905 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18905
                                                        in
                                                     let uu____18906 =
                                                       let uu____18909 =
                                                         let uu____18910 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18910
                                                          in
                                                       [uu____18909]  in
                                                     uu____18904 ::
                                                       uu____18906
                                                      in
                                                   (bind1, uu____18903)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18896
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18895
                                                in
                                             uu____18888
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18916 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18930 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18930
                                         then
                                           let uu____18941 =
                                             let uu____18950 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18950
                                              in
                                           let uu____18951 =
                                             let uu____18962 =
                                               let uu____18971 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18971
                                                in
                                             [uu____18962]  in
                                           uu____18941 :: uu____18951
                                         else []  in
                                       let reified =
                                         let uu____19008 =
                                           let uu____19015 =
                                             let uu____19016 =
                                               let uu____19033 =
                                                 let uu____19044 =
                                                   let uu____19055 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____19064 =
                                                     let uu____19075 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____19075]  in
                                                   uu____19055 :: uu____19064
                                                    in
                                                 let uu____19108 =
                                                   let uu____19119 =
                                                     let uu____19130 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____19139 =
                                                       let uu____19150 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____19159 =
                                                         let uu____19170 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____19179 =
                                                           let uu____19190 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____19190]  in
                                                         uu____19170 ::
                                                           uu____19179
                                                          in
                                                       uu____19150 ::
                                                         uu____19159
                                                        in
                                                     uu____19130 ::
                                                       uu____19139
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____19119
                                                    in
                                                 FStar_List.append
                                                   uu____19044 uu____19108
                                                  in
                                               (bind_inst, uu____19033)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____19016
                                              in
                                           FStar_Syntax_Syntax.mk uu____19015
                                            in
                                         uu____19008
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____19274  ->
                                            let uu____19275 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____19276 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____19275 uu____19276);
                                       (let uu____19277 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____19277 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____19305 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____19305
                        in
                     let uu____19306 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____19306 with
                      | (uu____19307,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____19344 =
                                  let uu____19345 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____19345.FStar_Syntax_Syntax.n  in
                                match uu____19344 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____19349) -> t2
                                | uu____19354 -> head4  in
                              let uu____19355 =
                                let uu____19356 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____19356.FStar_Syntax_Syntax.n  in
                              match uu____19355 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____19362 -> FStar_Pervasives_Native.None
                               in
                            let uu____19363 = maybe_extract_fv head4  in
                            match uu____19363 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____19373 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____19373
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____19378 = maybe_extract_fv head5
                                     in
                                  match uu____19378 with
                                  | FStar_Pervasives_Native.Some uu____19383
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____19384 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____19389 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____19406 =
                              match uu____19406 with
                              | (e,q) ->
                                  let uu____19419 =
                                    let uu____19420 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____19420.FStar_Syntax_Syntax.n  in
                                  (match uu____19419 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____19435 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____19435
                                   | uu____19436 -> false)
                               in
                            let uu____19437 =
                              let uu____19438 =
                                let uu____19449 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____19449 :: args  in
                              FStar_Util.for_some is_arg_impure uu____19438
                               in
                            if uu____19437
                            then
                              let uu____19474 =
                                let uu____19475 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____19475
                                 in
                              failwith uu____19474
                            else ());
                           (let uu____19477 = maybe_unfold_action head_app
                               in
                            match uu____19477 with
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
                                   (fun uu____19522  ->
                                      let uu____19523 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____19524 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____19523 uu____19524);
                                 (let uu____19525 = FStar_List.tl stack  in
                                  norm cfg env uu____19525 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____19527) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____19551 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____19551  in
                     (log cfg
                        (fun uu____19555  ->
                           let uu____19556 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____19556);
                      (let uu____19557 = FStar_List.tl stack  in
                       norm cfg env uu____19557 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____19678  ->
                               match uu____19678 with
                               | (pat,wopt,tm) ->
                                   let uu____19726 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____19726)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____19758 = FStar_List.tl stack  in
                     norm cfg env uu____19758 tm
                 | uu____19759 -> fallback ())

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
              (fun uu____19773  ->
                 let uu____19774 = FStar_Ident.string_of_lid msrc  in
                 let uu____19775 = FStar_Ident.string_of_lid mtgt  in
                 let uu____19776 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____19774
                   uu____19775 uu____19776);
            (let uu____19777 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____19777
             then
               let ed =
                 let uu____19779 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____19779  in
               let uu____19780 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____19780 with
               | (uu____19781,return_repr) ->
                   let return_inst =
                     let uu____19794 =
                       let uu____19795 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____19795.FStar_Syntax_Syntax.n  in
                     match uu____19794 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____19801::[]) ->
                         let uu____19806 =
                           let uu____19813 =
                             let uu____19814 =
                               let uu____19821 =
                                 let uu____19822 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____19822]  in
                               (return_tm, uu____19821)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____19814  in
                           FStar_Syntax_Syntax.mk uu____19813  in
                         uu____19806 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19828 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19831 =
                     let uu____19838 =
                       let uu____19839 =
                         let uu____19856 =
                           let uu____19867 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19876 =
                             let uu____19887 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19887]  in
                           uu____19867 :: uu____19876  in
                         (return_inst, uu____19856)  in
                       FStar_Syntax_Syntax.Tm_app uu____19839  in
                     FStar_Syntax_Syntax.mk uu____19838  in
                   uu____19831 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____19936 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____19936 with
                | FStar_Pervasives_Native.None  ->
                    let uu____19939 =
                      let uu____19940 = FStar_Ident.text_of_lid msrc  in
                      let uu____19941 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____19940 uu____19941
                       in
                    failwith uu____19939
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19942;
                      FStar_TypeChecker_Env.mtarget = uu____19943;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19944;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____19966 =
                      let uu____19967 = FStar_Ident.text_of_lid msrc  in
                      let uu____19968 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____19967 uu____19968
                       in
                    failwith uu____19966
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____19969;
                      FStar_TypeChecker_Env.mtarget = uu____19970;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____19971;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____20006 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____20007 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____20006 t FStar_Syntax_Syntax.tun uu____20007))

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
                (fun uu____20077  ->
                   match uu____20077 with
                   | (a,imp) ->
                       let uu____20096 = norm cfg env [] a  in
                       (uu____20096, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____20106  ->
             let uu____20107 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____20108 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____20107 uu____20108);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20132 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____20132
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___338_20135 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___338_20135.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___338_20135.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____20157 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____20157
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___339_20160 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___339_20160.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___339_20160.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____20205  ->
                      match uu____20205 with
                      | (a,i) ->
                          let uu____20224 = norm cfg env [] a  in
                          (uu____20224, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___254_20246  ->
                       match uu___254_20246 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____20250 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____20250
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___340_20258 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___341_20261 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___341_20261.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___340_20258.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___340_20258.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____20264  ->
        match uu____20264 with
        | (x,imp) ->
            let uu____20271 =
              let uu___342_20272 = x  in
              let uu____20273 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___342_20272.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___342_20272.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____20273
              }  in
            (uu____20271, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____20281 =
          FStar_List.fold_left
            (fun uu____20315  ->
               fun b  ->
                 match uu____20315 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____20281 with | (nbs,uu____20395) -> FStar_List.rev nbs

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
            let uu____20427 =
              let uu___343_20428 = rc  in
              let uu____20429 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___343_20428.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____20429;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___343_20428.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____20427
        | uu____20438 -> lopt

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
            (let uu____20461 = FStar_Syntax_Print.term_to_string tm  in
             let uu____20462 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____20461
               uu____20462)
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
          let uu____20488 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____20488
          then tm1
          else
            (let w t =
               let uu___344_20502 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___344_20502.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___344_20502.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____20513 =
                 let uu____20514 = FStar_Syntax_Util.unmeta t  in
                 uu____20514.FStar_Syntax_Syntax.n  in
               match uu____20513 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____20521 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____20582)::args1,(bv,uu____20585)::bs1) ->
                   let uu____20639 =
                     let uu____20640 = FStar_Syntax_Subst.compress t  in
                     uu____20640.FStar_Syntax_Syntax.n  in
                   (match uu____20639 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____20644 -> false)
               | ([],[]) -> true
               | (uu____20673,uu____20674) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____20723 = FStar_Syntax_Print.term_to_string t  in
                  let uu____20724 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____20723
                    uu____20724)
               else ();
               (let uu____20726 = FStar_Syntax_Util.head_and_args' t  in
                match uu____20726 with
                | (hd1,args) ->
                    let uu____20765 =
                      let uu____20766 = FStar_Syntax_Subst.compress hd1  in
                      uu____20766.FStar_Syntax_Syntax.n  in
                    (match uu____20765 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____20773 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____20774 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____20775 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____20773 uu____20774 uu____20775)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____20777 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____20794 = FStar_Syntax_Print.term_to_string t  in
                  let uu____20795 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____20794
                    uu____20795)
               else ();
               (let uu____20797 = FStar_Syntax_Util.is_squash t  in
                match uu____20797 with
                | FStar_Pervasives_Native.Some (uu____20808,t') ->
                    is_applied bs t'
                | uu____20820 ->
                    let uu____20829 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____20829 with
                     | FStar_Pervasives_Native.Some (uu____20840,t') ->
                         is_applied bs t'
                     | uu____20852 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____20876 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____20876 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____20883)::(q,uu____20885)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____20927 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____20928 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____20927 uu____20928)
                    else ();
                    (let uu____20930 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____20930 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20935 =
                           let uu____20936 = FStar_Syntax_Subst.compress p
                              in
                           uu____20936.FStar_Syntax_Syntax.n  in
                         (match uu____20935 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____20944 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20944))
                          | uu____20947 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____20950)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____20975 =
                           let uu____20976 = FStar_Syntax_Subst.compress p1
                              in
                           uu____20976.FStar_Syntax_Syntax.n  in
                         (match uu____20975 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____20984 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____20984))
                          | uu____20987 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____20991 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____20991 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____20996 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____20996 with
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
                                     let uu____21007 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21007))
                               | uu____21010 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____21015)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____21040 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____21040 with
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
                                     let uu____21051 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____21051))
                               | uu____21054 -> FStar_Pervasives_Native.None)
                          | uu____21057 -> FStar_Pervasives_Native.None)
                     | uu____21060 -> FStar_Pervasives_Native.None))
               | uu____21063 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____21076 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____21076 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____21082)::[],uu____21083,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____21102 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____21103 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____21102
                         uu____21103)
                    else ();
                    is_quantified_const bv phi')
               | uu____21105 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____21118 =
                 let uu____21119 = FStar_Syntax_Subst.compress phi  in
                 uu____21119.FStar_Syntax_Syntax.n  in
               match uu____21118 with
               | FStar_Syntax_Syntax.Tm_match (uu____21124,br::brs) ->
                   let uu____21191 = br  in
                   (match uu____21191 with
                    | (uu____21208,uu____21209,e) ->
                        let r =
                          let uu____21230 = simp_t e  in
                          match uu____21230 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____21236 =
                                FStar_List.for_all
                                  (fun uu____21254  ->
                                     match uu____21254 with
                                     | (uu____21267,uu____21268,e') ->
                                         let uu____21282 = simp_t e'  in
                                         uu____21282 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____21236
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____21290 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____21299 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____21299
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____21334 =
                 match uu____21334 with
                 | (t1,q) ->
                     let uu____21355 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____21355 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____21387 -> (t1, q))
                  in
               let uu____21400 = FStar_Syntax_Util.head_and_args t  in
               match uu____21400 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____21478 =
                 let uu____21479 = FStar_Syntax_Util.unmeta ty  in
                 uu____21479.FStar_Syntax_Syntax.n  in
               match uu____21478 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____21483) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____21488,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____21512 -> false  in
             let simplify1 arg =
               let uu____21543 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____21543, arg)  in
             let uu____21556 = is_forall_const tm1  in
             match uu____21556 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____21561 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____21562 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____21561
                       uu____21562)
                  else ();
                  (let uu____21564 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____21564))
             | FStar_Pervasives_Native.None  ->
                 let uu____21565 =
                   let uu____21566 = FStar_Syntax_Subst.compress tm1  in
                   uu____21566.FStar_Syntax_Syntax.n  in
                 (match uu____21565 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____21570;
                              FStar_Syntax_Syntax.vars = uu____21571;_},uu____21572);
                         FStar_Syntax_Syntax.pos = uu____21573;
                         FStar_Syntax_Syntax.vars = uu____21574;_},args)
                      ->
                      let uu____21604 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21604
                      then
                        let uu____21605 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21605 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21660)::
                             (uu____21661,(arg,uu____21663))::[] ->
                             maybe_auto_squash arg
                         | (uu____21728,(arg,uu____21730))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21731)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21796)::uu____21797::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21860::(FStar_Pervasives_Native.Some (false
                                         ),uu____21861)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21924 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21940 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21940
                         then
                           let uu____21941 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21941 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21996)::uu____21997::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22060::(FStar_Pervasives_Native.Some (true
                                           ),uu____22061)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22124)::(uu____22125,(arg,uu____22127))::[]
                               -> maybe_auto_squash arg
                           | (uu____22192,(arg,uu____22194))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22195)::[]
                               -> maybe_auto_squash arg
                           | uu____22260 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22276 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22276
                            then
                              let uu____22277 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22277 with
                              | uu____22332::(FStar_Pervasives_Native.Some
                                              (true ),uu____22333)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22396)::uu____22397::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22460)::(uu____22461,(arg,uu____22463))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22528,(p,uu____22530))::(uu____22531,
                                                                (q,uu____22533))::[]
                                  ->
                                  let uu____22598 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22598
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22600 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22616 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22616
                               then
                                 let uu____22617 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22617 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22672)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22673)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22738)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22739)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22804)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22805)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22870)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22871)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22936,(arg,uu____22938))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22939)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23004)::(uu____23005,(arg,uu____23007))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23072,(arg,uu____23074))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23075)::[]
                                     ->
                                     let uu____23140 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23140
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23141)::(uu____23142,(arg,uu____23144))::[]
                                     ->
                                     let uu____23209 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23209
                                 | (uu____23210,(p,uu____23212))::(uu____23213,
                                                                   (q,uu____23215))::[]
                                     ->
                                     let uu____23280 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23280
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23282 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23298 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23298
                                  then
                                    let uu____23299 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23299 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23354)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23393)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23432 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23448 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23448
                                     then
                                       match args with
                                       | (t,uu____23450)::[] ->
                                           let uu____23475 =
                                             let uu____23476 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23476.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23475 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23479::[],body,uu____23481)
                                                ->
                                                let uu____23516 = simp_t body
                                                   in
                                                (match uu____23516 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23519 -> tm1)
                                            | uu____23522 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23524))::(t,uu____23526)::[]
                                           ->
                                           let uu____23565 =
                                             let uu____23566 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23566.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23565 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23569::[],body,uu____23571)
                                                ->
                                                let uu____23606 = simp_t body
                                                   in
                                                (match uu____23606 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23609 -> tm1)
                                            | uu____23612 -> tm1)
                                       | uu____23613 -> tm1
                                     else
                                       (let uu____23625 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23625
                                        then
                                          match args with
                                          | (t,uu____23627)::[] ->
                                              let uu____23652 =
                                                let uu____23653 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23653.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23652 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23656::[],body,uu____23658)
                                                   ->
                                                   let uu____23693 =
                                                     simp_t body  in
                                                   (match uu____23693 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23696 -> tm1)
                                               | uu____23699 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23701))::(t,uu____23703)::[]
                                              ->
                                              let uu____23742 =
                                                let uu____23743 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23743.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23742 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23746::[],body,uu____23748)
                                                   ->
                                                   let uu____23783 =
                                                     simp_t body  in
                                                   (match uu____23783 with
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
                                                    | uu____23786 -> tm1)
                                               | uu____23789 -> tm1)
                                          | uu____23790 -> tm1
                                        else
                                          (let uu____23802 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23802
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23803;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23804;_},uu____23805)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23830;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23831;_},uu____23832)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23857 -> tm1
                                           else
                                             (let uu____23869 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____23869 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____23889 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____23901;
                         FStar_Syntax_Syntax.vars = uu____23902;_},args)
                      ->
                      let uu____23928 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____23928
                      then
                        let uu____23929 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____23929 with
                         | (FStar_Pervasives_Native.Some (true ),uu____23984)::
                             (uu____23985,(arg,uu____23987))::[] ->
                             maybe_auto_squash arg
                         | (uu____24052,(arg,uu____24054))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____24055)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____24120)::uu____24121::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____24184::(FStar_Pervasives_Native.Some (false
                                         ),uu____24185)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____24248 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____24264 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____24264
                         then
                           let uu____24265 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____24265 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____24320)::uu____24321::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____24384::(FStar_Pervasives_Native.Some (true
                                           ),uu____24385)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____24448)::(uu____24449,(arg,uu____24451))::[]
                               -> maybe_auto_squash arg
                           | (uu____24516,(arg,uu____24518))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____24519)::[]
                               -> maybe_auto_squash arg
                           | uu____24584 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____24600 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____24600
                            then
                              let uu____24601 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____24601 with
                              | uu____24656::(FStar_Pervasives_Native.Some
                                              (true ),uu____24657)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____24720)::uu____24721::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____24784)::(uu____24785,(arg,uu____24787))::[]
                                  -> maybe_auto_squash arg
                              | (uu____24852,(p,uu____24854))::(uu____24855,
                                                                (q,uu____24857))::[]
                                  ->
                                  let uu____24922 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____24922
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____24924 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____24940 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____24940
                               then
                                 let uu____24941 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____24941 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____24996)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____24997)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25062)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25063)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25128)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____25129)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25194)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____25195)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____25260,(arg,uu____25262))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____25263)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____25328)::(uu____25329,(arg,uu____25331))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____25396,(arg,uu____25398))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____25399)::[]
                                     ->
                                     let uu____25464 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25464
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____25465)::(uu____25466,(arg,uu____25468))::[]
                                     ->
                                     let uu____25533 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____25533
                                 | (uu____25534,(p,uu____25536))::(uu____25537,
                                                                   (q,uu____25539))::[]
                                     ->
                                     let uu____25604 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____25604
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____25606 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____25622 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____25622
                                  then
                                    let uu____25623 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____25623 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____25678)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____25717)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____25756 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____25772 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____25772
                                     then
                                       match args with
                                       | (t,uu____25774)::[] ->
                                           let uu____25799 =
                                             let uu____25800 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____25800.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____25799 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____25803::[],body,uu____25805)
                                                ->
                                                let uu____25840 = simp_t body
                                                   in
                                                (match uu____25840 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____25843 -> tm1)
                                            | uu____25846 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____25848))::(t,uu____25850)::[]
                                           ->
                                           let uu____25889 =
                                             let uu____25890 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____25890.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____25889 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____25893::[],body,uu____25895)
                                                ->
                                                let uu____25930 = simp_t body
                                                   in
                                                (match uu____25930 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____25933 -> tm1)
                                            | uu____25936 -> tm1)
                                       | uu____25937 -> tm1
                                     else
                                       (let uu____25949 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____25949
                                        then
                                          match args with
                                          | (t,uu____25951)::[] ->
                                              let uu____25976 =
                                                let uu____25977 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____25977.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____25976 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____25980::[],body,uu____25982)
                                                   ->
                                                   let uu____26017 =
                                                     simp_t body  in
                                                   (match uu____26017 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____26020 -> tm1)
                                               | uu____26023 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____26025))::(t,uu____26027)::[]
                                              ->
                                              let uu____26066 =
                                                let uu____26067 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____26067.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26066 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____26070::[],body,uu____26072)
                                                   ->
                                                   let uu____26107 =
                                                     simp_t body  in
                                                   (match uu____26107 with
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
                                                    | uu____26110 -> tm1)
                                               | uu____26113 -> tm1)
                                          | uu____26114 -> tm1
                                        else
                                          (let uu____26126 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____26126
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26127;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26128;_},uu____26129)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____26154;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____26155;_},uu____26156)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____26181 -> tm1
                                           else
                                             (let uu____26193 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____26193 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____26213 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____26230 = simp_t t  in
                      (match uu____26230 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____26233 ->
                      let uu____26256 = is_const_match tm1  in
                      (match uu____26256 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____26259 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____26269  ->
               (let uu____26271 = FStar_Syntax_Print.tag_of_term t  in
                let uu____26272 = FStar_Syntax_Print.term_to_string t  in
                let uu____26273 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____26280 =
                  let uu____26281 =
                    let uu____26284 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____26284
                     in
                  stack_to_string uu____26281  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____26271 uu____26272 uu____26273 uu____26280);
               (let uu____26307 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____26307
                then
                  let uu____26308 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____26308 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____26315 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____26316 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____26317 =
                          let uu____26318 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____26318
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____26315
                          uu____26316 uu____26317);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____26336 =
                     let uu____26337 =
                       let uu____26338 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____26338  in
                     FStar_Util.string_of_int uu____26337  in
                   let uu____26343 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____26344 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____26336 uu____26343 uu____26344)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____26350,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____26401  ->
                     let uu____26402 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____26402);
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
               let uu____26440 =
                 let uu___345_26441 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___345_26441.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___345_26441.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____26440
           | (Arg (Univ uu____26444,uu____26445,uu____26446))::uu____26447 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____26450,uu____26451))::uu____26452 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____26467,uu____26468),aq,r))::stack1
               when
               let uu____26518 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____26518 ->
               let t2 =
                 let uu____26522 =
                   let uu____26527 =
                     let uu____26528 = closure_as_term cfg env_arg tm  in
                     (uu____26528, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____26527  in
                 uu____26522 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____26540),aq,r))::stack1 ->
               (log cfg
                  (fun uu____26593  ->
                     let uu____26594 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____26594);
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
                  (let uu____26608 = FStar_ST.op_Bang m  in
                   match uu____26608 with
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
                   | FStar_Pervasives_Native.Some (uu____26749,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____26804 =
                 log cfg
                   (fun uu____26808  ->
                      let uu____26809 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____26809);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____26817 =
                 let uu____26818 = FStar_Syntax_Subst.compress t1  in
                 uu____26818.FStar_Syntax_Syntax.n  in
               (match uu____26817 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____26845 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____26845  in
                    (log cfg
                       (fun uu____26849  ->
                          let uu____26850 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____26850);
                     (let uu____26851 = FStar_List.tl stack  in
                      norm cfg env1 uu____26851 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____26852);
                       FStar_Syntax_Syntax.pos = uu____26853;
                       FStar_Syntax_Syntax.vars = uu____26854;_},(e,uu____26856)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____26895 when
                    (cfg.steps).primops ->
                    let uu____26912 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____26912 with
                     | (hd1,args) ->
                         let uu____26955 =
                           let uu____26956 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____26956.FStar_Syntax_Syntax.n  in
                         (match uu____26955 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____26960 = find_prim_step cfg fv  in
                              (match uu____26960 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____26963; arity = uu____26964;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____26966;
                                     requires_binder_substitution =
                                       uu____26967;
                                     interpretation = uu____26968;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____26985 -> fallback " (3)" ())
                          | uu____26988 -> fallback " (4)" ()))
                | uu____26989 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____27014  ->
                     let uu____27015 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____27015);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____27024 =
                   log cfg1
                     (fun uu____27029  ->
                        let uu____27030 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____27031 =
                          let uu____27032 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____27059  ->
                                    match uu____27059 with
                                    | (p,uu____27069,uu____27070) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____27032
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____27030 uu____27031);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___255_27087  ->
                                match uu___255_27087 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____27088 -> false))
                         in
                      let steps =
                        let uu___346_27090 = cfg1.steps  in
                        {
                          beta = (uu___346_27090.beta);
                          iota = (uu___346_27090.iota);
                          zeta = false;
                          weak = (uu___346_27090.weak);
                          hnf = (uu___346_27090.hnf);
                          primops = (uu___346_27090.primops);
                          do_not_unfold_pure_lets =
                            (uu___346_27090.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___346_27090.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___346_27090.pure_subterms_within_computations);
                          simplify = (uu___346_27090.simplify);
                          erase_universes = (uu___346_27090.erase_universes);
                          allow_unbound_universes =
                            (uu___346_27090.allow_unbound_universes);
                          reify_ = (uu___346_27090.reify_);
                          compress_uvars = (uu___346_27090.compress_uvars);
                          no_full_norm = (uu___346_27090.no_full_norm);
                          check_no_uvars = (uu___346_27090.check_no_uvars);
                          unmeta = (uu___346_27090.unmeta);
                          unascribe = (uu___346_27090.unascribe);
                          in_full_norm_request =
                            (uu___346_27090.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___346_27090.weakly_reduce_scrutinee)
                        }  in
                      let uu___347_27095 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___347_27095.tcenv);
                        debug = (uu___347_27095.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___347_27095.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___347_27095.memoize_lazy);
                        normalize_pure_lets =
                          (uu___347_27095.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____27167 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____27196 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____27280  ->
                                    fun uu____27281  ->
                                      match (uu____27280, uu____27281) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____27420 = norm_pat env3 p1
                                             in
                                          (match uu____27420 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____27196 with
                           | (pats1,env3) ->
                               ((let uu___348_27582 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___348_27582.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___349_27601 = x  in
                            let uu____27602 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___349_27601.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___349_27601.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27602
                            }  in
                          ((let uu___350_27616 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___350_27616.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___351_27627 = x  in
                            let uu____27628 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___351_27627.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___351_27627.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27628
                            }  in
                          ((let uu___352_27642 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___352_27642.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___353_27658 = x  in
                            let uu____27659 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___353_27658.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___353_27658.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____27659
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___354_27674 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___354_27674.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____27718 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____27748 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____27748 with
                                  | (p,wopt,e) ->
                                      let uu____27768 = norm_pat env1 p  in
                                      (match uu____27768 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____27823 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____27823
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____27840 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____27840
                      then
                        norm
                          (let uu___355_27845 = cfg1  in
                           {
                             steps =
                               (let uu___356_27848 = cfg1.steps  in
                                {
                                  beta = (uu___356_27848.beta);
                                  iota = (uu___356_27848.iota);
                                  zeta = (uu___356_27848.zeta);
                                  weak = (uu___356_27848.weak);
                                  hnf = (uu___356_27848.hnf);
                                  primops = (uu___356_27848.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___356_27848.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___356_27848.unfold_until);
                                  unfold_only = (uu___356_27848.unfold_only);
                                  unfold_fully =
                                    (uu___356_27848.unfold_fully);
                                  unfold_attr = (uu___356_27848.unfold_attr);
                                  unfold_tac = (uu___356_27848.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___356_27848.pure_subterms_within_computations);
                                  simplify = (uu___356_27848.simplify);
                                  erase_universes =
                                    (uu___356_27848.erase_universes);
                                  allow_unbound_universes =
                                    (uu___356_27848.allow_unbound_universes);
                                  reify_ = (uu___356_27848.reify_);
                                  compress_uvars =
                                    (uu___356_27848.compress_uvars);
                                  no_full_norm =
                                    (uu___356_27848.no_full_norm);
                                  check_no_uvars =
                                    (uu___356_27848.check_no_uvars);
                                  unmeta = (uu___356_27848.unmeta);
                                  unascribe = (uu___356_27848.unascribe);
                                  in_full_norm_request =
                                    (uu___356_27848.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___355_27845.tcenv);
                             debug = (uu___355_27845.debug);
                             delta_level = (uu___355_27845.delta_level);
                             primitive_steps =
                               (uu___355_27845.primitive_steps);
                             strong = (uu___355_27845.strong);
                             memoize_lazy = (uu___355_27845.memoize_lazy);
                             normalize_pure_lets =
                               (uu___355_27845.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____27850 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____27850)
                    in
                 let rec is_cons head1 =
                   let uu____27875 =
                     let uu____27876 = FStar_Syntax_Subst.compress head1  in
                     uu____27876.FStar_Syntax_Syntax.n  in
                   match uu____27875 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____27880) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____27885 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____27886;
                         FStar_Syntax_Syntax.fv_delta = uu____27887;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____27888;
                         FStar_Syntax_Syntax.fv_delta = uu____27889;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____27890);_}
                       -> true
                   | uu____27897 -> false  in
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
                   let uu____28060 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____28060 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____28153 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____28192 ->
                                 let uu____28193 =
                                   let uu____28194 = is_cons head1  in
                                   Prims.op_Negation uu____28194  in
                                 FStar_Util.Inr uu____28193)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____28219 =
                              let uu____28220 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____28220.FStar_Syntax_Syntax.n  in
                            (match uu____28219 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____28238 ->
                                 let uu____28239 =
                                   let uu____28240 = is_cons head1  in
                                   Prims.op_Negation uu____28240  in
                                 FStar_Util.Inr uu____28239))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____28323)::rest_a,(p1,uu____28326)::rest_p) ->
                       let uu____28380 = matches_pat t2 p1  in
                       (match uu____28380 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____28429 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____28549 = matches_pat scrutinee1 p1  in
                       (match uu____28549 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____28589  ->
                                  let uu____28590 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____28591 =
                                    let uu____28592 =
                                      FStar_List.map
                                        (fun uu____28602  ->
                                           match uu____28602 with
                                           | (uu____28607,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____28592
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____28590 uu____28591);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____28639  ->
                                       match uu____28639 with
                                       | (bv,t2) ->
                                           let uu____28662 =
                                             let uu____28669 =
                                               let uu____28672 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____28672
                                                in
                                             let uu____28673 =
                                               let uu____28674 =
                                                 let uu____28705 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____28705, false)
                                                  in
                                               Clos uu____28674  in
                                             (uu____28669, uu____28673)  in
                                           uu____28662 :: env2) env1 s
                                 in
                              let uu____28818 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____28818)))
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
    let uu____28845 =
      let uu____28848 = FStar_ST.op_Bang plugins  in p :: uu____28848  in
    FStar_ST.op_Colon_Equals plugins uu____28845  in
  let retrieve uu____28948 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____29021  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___256_29062  ->
                  match uu___256_29062 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | uu____29066 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____29072 -> d  in
        let uu____29075 = to_fsteps s  in
        let uu____29076 =
          let uu____29077 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____29078 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____29079 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Unfolding")
             in
          let uu____29080 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____29081 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____29082 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____29083 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____29077;
            primop = uu____29078;
            unfolding = uu____29079;
            b380 = uu____29080;
            wpe = uu____29081;
            norm_delayed = uu____29082;
            print_normalized = uu____29083
          }  in
        let uu____29084 =
          let uu____29087 =
            let uu____29090 = retrieve_plugins ()  in
            FStar_List.append uu____29090 psteps  in
          add_steps built_in_primitive_steps uu____29087  in
        let uu____29093 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____29095 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____29095)
           in
        {
          steps = uu____29075;
          tcenv = e;
          debug = uu____29076;
          delta_level = d1;
          primitive_steps = uu____29084;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____29093
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
            (fun uu____29144  ->
               let uu____29145 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "Starting normalizer for (%s)\n" uu____29145);
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
      fun t  -> let uu____29182 = config s e  in norm_comp uu____29182 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____29199 = config [] env  in norm_universe uu____29199 [] u
  
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
        let uu____29223 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29223  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____29230 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___357_29249 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___357_29249.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___357_29249.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____29256 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____29256
          then
            let ct1 =
              let uu____29258 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____29258 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____29265 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____29265
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___358_29269 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___358_29269.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___358_29269.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___358_29269.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___359_29271 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___359_29271.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___359_29271.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___359_29271.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___359_29271.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___360_29272 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___360_29272.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___360_29272.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____29274 -> c
  
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
        let uu____29292 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____29292  in
      let uu____29299 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____29299
      then
        let uu____29300 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____29300 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____29306  ->
                 let uu____29307 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____29307)
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
            ((let uu____29328 =
                let uu____29333 =
                  let uu____29334 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29334
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29333)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____29328);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____29349 = config [AllowUnboundUniverses] env  in
          norm_comp uu____29349 [] c
        with
        | e ->
            ((let uu____29362 =
                let uu____29367 =
                  let uu____29368 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____29368
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____29367)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____29362);
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
                   let uu____29413 =
                     let uu____29414 =
                       let uu____29421 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____29421)  in
                     FStar_Syntax_Syntax.Tm_refine uu____29414  in
                   mk uu____29413 t01.FStar_Syntax_Syntax.pos
               | uu____29426 -> t2)
          | uu____29427 -> t2  in
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
        let uu____29506 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____29506 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____29543 ->
                 let uu____29552 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____29552 with
                  | (actuals,uu____29562,uu____29563) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____29581 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____29581 with
                         | (binders,args) ->
                             let uu____29592 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____29592
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
      | uu____29606 ->
          let uu____29607 = FStar_Syntax_Util.head_and_args t  in
          (match uu____29607 with
           | (head1,args) ->
               let uu____29650 =
                 let uu____29651 = FStar_Syntax_Subst.compress head1  in
                 uu____29651.FStar_Syntax_Syntax.n  in
               (match uu____29650 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____29672 =
                      let uu____29687 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____29687  in
                    (match uu____29672 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____29725 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___365_29733 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___365_29733.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___365_29733.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___365_29733.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___365_29733.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___365_29733.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___365_29733.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___365_29733.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___365_29733.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___365_29733.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___365_29733.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___365_29733.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___365_29733.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___365_29733.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___365_29733.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___365_29733.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___365_29733.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___365_29733.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___365_29733.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___365_29733.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___365_29733.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___365_29733.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___365_29733.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___365_29733.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___365_29733.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___365_29733.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___365_29733.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___365_29733.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___365_29733.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___365_29733.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___365_29733.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___365_29733.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___365_29733.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___365_29733.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___365_29733.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___365_29733.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___365_29733.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___365_29733.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___365_29733.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____29725 with
                            | (uu____29734,ty,uu____29736) ->
                                eta_expand_with_type env t ty))
                | uu____29737 ->
                    let uu____29738 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___366_29746 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___366_29746.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___366_29746.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___366_29746.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___366_29746.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___366_29746.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___366_29746.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___366_29746.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___366_29746.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___366_29746.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___366_29746.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___366_29746.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___366_29746.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___366_29746.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___366_29746.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___366_29746.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___366_29746.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___366_29746.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___366_29746.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___366_29746.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___366_29746.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___366_29746.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___366_29746.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___366_29746.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___366_29746.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___366_29746.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___366_29746.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___366_29746.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___366_29746.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___366_29746.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___366_29746.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___366_29746.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___366_29746.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___366_29746.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___366_29746.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___366_29746.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___366_29746.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___366_29746.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___366_29746.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____29738 with
                     | (uu____29747,ty,uu____29749) ->
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
      let uu___367_29830 = x  in
      let uu____29831 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___367_29830.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___367_29830.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____29831
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____29834 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____29857 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____29858 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____29859 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____29860 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____29867 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____29868 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____29869 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___368_29903 = rc  in
          let uu____29904 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____29913 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___368_29903.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____29904;
            FStar_Syntax_Syntax.residual_flags = uu____29913
          }  in
        let uu____29916 =
          let uu____29917 =
            let uu____29936 = elim_delayed_subst_binders bs  in
            let uu____29945 = elim_delayed_subst_term t2  in
            let uu____29948 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____29936, uu____29945, uu____29948)  in
          FStar_Syntax_Syntax.Tm_abs uu____29917  in
        mk1 uu____29916
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____29985 =
          let uu____29986 =
            let uu____30001 = elim_delayed_subst_binders bs  in
            let uu____30010 = elim_delayed_subst_comp c  in
            (uu____30001, uu____30010)  in
          FStar_Syntax_Syntax.Tm_arrow uu____29986  in
        mk1 uu____29985
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____30029 =
          let uu____30030 =
            let uu____30037 = elim_bv bv  in
            let uu____30038 = elim_delayed_subst_term phi  in
            (uu____30037, uu____30038)  in
          FStar_Syntax_Syntax.Tm_refine uu____30030  in
        mk1 uu____30029
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____30069 =
          let uu____30070 =
            let uu____30087 = elim_delayed_subst_term t2  in
            let uu____30090 = elim_delayed_subst_args args  in
            (uu____30087, uu____30090)  in
          FStar_Syntax_Syntax.Tm_app uu____30070  in
        mk1 uu____30069
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___369_30162 = p  in
              let uu____30163 =
                let uu____30164 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____30164  in
              {
                FStar_Syntax_Syntax.v = uu____30163;
                FStar_Syntax_Syntax.p =
                  (uu___369_30162.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___370_30166 = p  in
              let uu____30167 =
                let uu____30168 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____30168  in
              {
                FStar_Syntax_Syntax.v = uu____30167;
                FStar_Syntax_Syntax.p =
                  (uu___370_30166.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___371_30175 = p  in
              let uu____30176 =
                let uu____30177 =
                  let uu____30184 = elim_bv x  in
                  let uu____30185 = elim_delayed_subst_term t0  in
                  (uu____30184, uu____30185)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____30177  in
              {
                FStar_Syntax_Syntax.v = uu____30176;
                FStar_Syntax_Syntax.p =
                  (uu___371_30175.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___372_30208 = p  in
              let uu____30209 =
                let uu____30210 =
                  let uu____30223 =
                    FStar_List.map
                      (fun uu____30246  ->
                         match uu____30246 with
                         | (x,b) ->
                             let uu____30259 = elim_pat x  in
                             (uu____30259, b)) pats
                     in
                  (fv, uu____30223)  in
                FStar_Syntax_Syntax.Pat_cons uu____30210  in
              {
                FStar_Syntax_Syntax.v = uu____30209;
                FStar_Syntax_Syntax.p =
                  (uu___372_30208.FStar_Syntax_Syntax.p)
              }
          | uu____30272 -> p  in
        let elim_branch uu____30296 =
          match uu____30296 with
          | (pat,wopt,t3) ->
              let uu____30322 = elim_pat pat  in
              let uu____30325 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____30328 = elim_delayed_subst_term t3  in
              (uu____30322, uu____30325, uu____30328)
           in
        let uu____30333 =
          let uu____30334 =
            let uu____30357 = elim_delayed_subst_term t2  in
            let uu____30360 = FStar_List.map elim_branch branches  in
            (uu____30357, uu____30360)  in
          FStar_Syntax_Syntax.Tm_match uu____30334  in
        mk1 uu____30333
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____30491 =
          match uu____30491 with
          | (tc,topt) ->
              let uu____30526 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____30536 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____30536
                | FStar_Util.Inr c ->
                    let uu____30538 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____30538
                 in
              let uu____30539 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____30526, uu____30539)
           in
        let uu____30548 =
          let uu____30549 =
            let uu____30576 = elim_delayed_subst_term t2  in
            let uu____30579 = elim_ascription a  in
            (uu____30576, uu____30579, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____30549  in
        mk1 uu____30548
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___373_30640 = lb  in
          let uu____30641 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____30644 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___373_30640.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___373_30640.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____30641;
            FStar_Syntax_Syntax.lbeff =
              (uu___373_30640.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____30644;
            FStar_Syntax_Syntax.lbattrs =
              (uu___373_30640.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___373_30640.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____30647 =
          let uu____30648 =
            let uu____30661 =
              let uu____30668 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____30668)  in
            let uu____30677 = elim_delayed_subst_term t2  in
            (uu____30661, uu____30677)  in
          FStar_Syntax_Syntax.Tm_let uu____30648  in
        mk1 uu____30647
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____30721 =
          let uu____30722 =
            let uu____30729 = elim_delayed_subst_term tm  in
            (uu____30729, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____30722  in
        mk1 uu____30721
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____30740 =
          let uu____30741 =
            let uu____30748 = elim_delayed_subst_term t2  in
            let uu____30751 = elim_delayed_subst_meta md  in
            (uu____30748, uu____30751)  in
          FStar_Syntax_Syntax.Tm_meta uu____30741  in
        mk1 uu____30740

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___257_30760  ->
         match uu___257_30760 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____30764 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____30764
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
        let uu____30787 =
          let uu____30788 =
            let uu____30797 = elim_delayed_subst_term t  in
            (uu____30797, uopt)  in
          FStar_Syntax_Syntax.Total uu____30788  in
        mk1 uu____30787
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____30814 =
          let uu____30815 =
            let uu____30824 = elim_delayed_subst_term t  in
            (uu____30824, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____30815  in
        mk1 uu____30814
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___374_30833 = ct  in
          let uu____30834 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____30837 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____30848 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___374_30833.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___374_30833.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____30834;
            FStar_Syntax_Syntax.effect_args = uu____30837;
            FStar_Syntax_Syntax.flags = uu____30848
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___258_30851  ->
    match uu___258_30851 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____30865 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____30865
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____30904 =
          let uu____30911 = elim_delayed_subst_term t  in (m, uu____30911)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____30904
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____30923 =
          let uu____30932 = elim_delayed_subst_term t  in
          (m1, m2, uu____30932)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____30923
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
      (fun uu____30965  ->
         match uu____30965 with
         | (t,q) ->
             let uu____30984 = elim_delayed_subst_term t  in (uu____30984, q))
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
      (fun uu____31012  ->
         match uu____31012 with
         | (x,q) ->
             let uu____31031 =
               let uu___375_31032 = x  in
               let uu____31033 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___375_31032.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___375_31032.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____31033
               }  in
             (uu____31031, q)) bs

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
            | (uu____31139,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____31171,FStar_Util.Inl t) ->
                let uu____31193 =
                  let uu____31200 =
                    let uu____31201 =
                      let uu____31216 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____31216)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____31201  in
                  FStar_Syntax_Syntax.mk uu____31200  in
                uu____31193 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____31232 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____31232 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____31264 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____31337 ->
                    let uu____31338 =
                      let uu____31347 =
                        let uu____31348 = FStar_Syntax_Subst.compress t4  in
                        uu____31348.FStar_Syntax_Syntax.n  in
                      (uu____31347, tc)  in
                    (match uu____31338 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____31377) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____31424) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____31469,FStar_Util.Inl uu____31470) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____31501 -> failwith "Impossible")
                 in
              (match uu____31264 with
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
          let uu____31638 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____31638 with
          | (univ_names1,binders1,tc) ->
              let uu____31712 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____31712)
  
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
          let uu____31765 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____31765 with
          | (univ_names1,binders1,tc) ->
              let uu____31839 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____31839)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____31880 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____31880 with
           | (univ_names1,binders1,typ1) ->
               let uu___376_31920 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___376_31920.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___376_31920.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___376_31920.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___376_31920.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___377_31935 = s  in
          let uu____31936 =
            let uu____31937 =
              let uu____31946 = FStar_List.map (elim_uvars env) sigs  in
              (uu____31946, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____31937  in
          {
            FStar_Syntax_Syntax.sigel = uu____31936;
            FStar_Syntax_Syntax.sigrng =
              (uu___377_31935.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___377_31935.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___377_31935.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___377_31935.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____31963 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____31963 with
           | (univ_names1,uu____31987,typ1) ->
               let uu___378_32009 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___378_32009.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___378_32009.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___378_32009.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___378_32009.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____32015 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____32015 with
           | (univ_names1,uu____32039,typ1) ->
               let uu___379_32061 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___379_32061.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___379_32061.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___379_32061.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___379_32061.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____32089 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____32089 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____32114 =
                            let uu____32115 =
                              let uu____32116 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____32116  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____32115
                             in
                          elim_delayed_subst_term uu____32114  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___380_32119 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___380_32119.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___380_32119.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___380_32119.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___380_32119.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___381_32120 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___381_32120.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___381_32120.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___381_32120.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___381_32120.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___382_32126 = s  in
          let uu____32127 =
            let uu____32128 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____32128  in
          {
            FStar_Syntax_Syntax.sigel = uu____32127;
            FStar_Syntax_Syntax.sigrng =
              (uu___382_32126.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___382_32126.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___382_32126.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___382_32126.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____32132 = elim_uvars_aux_t env us [] t  in
          (match uu____32132 with
           | (us1,uu____32156,t1) ->
               let uu___383_32178 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___383_32178.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___383_32178.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___383_32178.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___383_32178.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____32179 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____32181 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____32181 with
           | (univs1,binders,signature) ->
               let uu____32221 =
                 let uu____32226 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____32226 with
                 | (univs_opening,univs2) ->
                     let uu____32249 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____32249)
                  in
               (match uu____32221 with
                | (univs_opening,univs_closing) ->
                    let uu____32252 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____32258 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____32259 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____32258, uu____32259)  in
                    (match uu____32252 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____32285 =
                           match uu____32285 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____32303 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____32303 with
                                | (us1,t1) ->
                                    let uu____32314 =
                                      let uu____32323 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____32334 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____32323, uu____32334)  in
                                    (match uu____32314 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____32363 =
                                           let uu____32372 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____32383 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____32372, uu____32383)  in
                                         (match uu____32363 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____32413 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____32413
                                                 in
                                              let uu____32414 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____32414 with
                                               | (uu____32441,uu____32442,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____32465 =
                                                       let uu____32466 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____32466
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____32465
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____32475 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____32475 with
                           | (uu____32494,uu____32495,t1) -> t1  in
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
                             | uu____32571 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____32598 =
                               let uu____32599 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____32599.FStar_Syntax_Syntax.n  in
                             match uu____32598 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____32658 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____32691 =
                               let uu____32692 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____32692.FStar_Syntax_Syntax.n  in
                             match uu____32691 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____32715) ->
                                 let uu____32740 = destruct_action_body body
                                    in
                                 (match uu____32740 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____32789 ->
                                 let uu____32790 = destruct_action_body t  in
                                 (match uu____32790 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____32845 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____32845 with
                           | (action_univs,t) ->
                               let uu____32854 = destruct_action_typ_templ t
                                  in
                               (match uu____32854 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___384_32901 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___384_32901.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___384_32901.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___385_32903 = ed  in
                           let uu____32904 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____32905 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____32906 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____32907 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____32908 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____32909 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____32910 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____32911 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____32912 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____32913 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____32914 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____32915 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____32916 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____32917 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___385_32903.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___385_32903.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____32904;
                             FStar_Syntax_Syntax.bind_wp = uu____32905;
                             FStar_Syntax_Syntax.if_then_else = uu____32906;
                             FStar_Syntax_Syntax.ite_wp = uu____32907;
                             FStar_Syntax_Syntax.stronger = uu____32908;
                             FStar_Syntax_Syntax.close_wp = uu____32909;
                             FStar_Syntax_Syntax.assert_p = uu____32910;
                             FStar_Syntax_Syntax.assume_p = uu____32911;
                             FStar_Syntax_Syntax.null_wp = uu____32912;
                             FStar_Syntax_Syntax.trivial = uu____32913;
                             FStar_Syntax_Syntax.repr = uu____32914;
                             FStar_Syntax_Syntax.return_repr = uu____32915;
                             FStar_Syntax_Syntax.bind_repr = uu____32916;
                             FStar_Syntax_Syntax.actions = uu____32917;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___385_32903.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___386_32920 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___386_32920.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___386_32920.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___386_32920.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___386_32920.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___259_32941 =
            match uu___259_32941 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____32972 = elim_uvars_aux_t env us [] t  in
                (match uu____32972 with
                 | (us1,uu____33004,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___387_33035 = sub_eff  in
            let uu____33036 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____33039 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___387_33035.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___387_33035.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____33036;
              FStar_Syntax_Syntax.lift = uu____33039
            }  in
          let uu___388_33042 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___388_33042.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___388_33042.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___388_33042.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___388_33042.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____33052 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____33052 with
           | (univ_names1,binders1,comp1) ->
               let uu___389_33092 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___389_33092.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___389_33092.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___389_33092.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___389_33092.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____33095 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____33096 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  