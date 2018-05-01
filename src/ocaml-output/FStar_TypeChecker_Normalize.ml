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
  | Unascribe [@@deriving show]
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
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____248 'Auu____249 .
    ('Auu____248 -> 'Auu____249) ->
      'Auu____249 ->
        'Auu____248 FStar_Pervasives_Native.option -> 'Auu____249
  =
  fun f  ->
    fun d  ->
      fun uu___105_269  ->
        match uu___105_269 with
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
  weakly_reduce_scrutinee: Prims.bool }[@@deriving show]
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
      let add_opt x uu___106_1503 =
        match uu___106_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___124_1523 = fs  in
          {
            beta = true;
            iota = (uu___124_1523.iota);
            zeta = (uu___124_1523.zeta);
            weak = (uu___124_1523.weak);
            hnf = (uu___124_1523.hnf);
            primops = (uu___124_1523.primops);
            do_not_unfold_pure_lets = (uu___124_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___124_1523.unfold_until);
            unfold_only = (uu___124_1523.unfold_only);
            unfold_fully = (uu___124_1523.unfold_fully);
            unfold_attr = (uu___124_1523.unfold_attr);
            unfold_tac = (uu___124_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___124_1523.pure_subterms_within_computations);
            simplify = (uu___124_1523.simplify);
            erase_universes = (uu___124_1523.erase_universes);
            allow_unbound_universes = (uu___124_1523.allow_unbound_universes);
            reify_ = (uu___124_1523.reify_);
            compress_uvars = (uu___124_1523.compress_uvars);
            no_full_norm = (uu___124_1523.no_full_norm);
            check_no_uvars = (uu___124_1523.check_no_uvars);
            unmeta = (uu___124_1523.unmeta);
            unascribe = (uu___124_1523.unascribe);
            in_full_norm_request = (uu___124_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___124_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___125_1524 = fs  in
          {
            beta = (uu___125_1524.beta);
            iota = true;
            zeta = (uu___125_1524.zeta);
            weak = (uu___125_1524.weak);
            hnf = (uu___125_1524.hnf);
            primops = (uu___125_1524.primops);
            do_not_unfold_pure_lets = (uu___125_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___125_1524.unfold_until);
            unfold_only = (uu___125_1524.unfold_only);
            unfold_fully = (uu___125_1524.unfold_fully);
            unfold_attr = (uu___125_1524.unfold_attr);
            unfold_tac = (uu___125_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___125_1524.pure_subterms_within_computations);
            simplify = (uu___125_1524.simplify);
            erase_universes = (uu___125_1524.erase_universes);
            allow_unbound_universes = (uu___125_1524.allow_unbound_universes);
            reify_ = (uu___125_1524.reify_);
            compress_uvars = (uu___125_1524.compress_uvars);
            no_full_norm = (uu___125_1524.no_full_norm);
            check_no_uvars = (uu___125_1524.check_no_uvars);
            unmeta = (uu___125_1524.unmeta);
            unascribe = (uu___125_1524.unascribe);
            in_full_norm_request = (uu___125_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___125_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___126_1525 = fs  in
          {
            beta = (uu___126_1525.beta);
            iota = (uu___126_1525.iota);
            zeta = true;
            weak = (uu___126_1525.weak);
            hnf = (uu___126_1525.hnf);
            primops = (uu___126_1525.primops);
            do_not_unfold_pure_lets = (uu___126_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1525.unfold_until);
            unfold_only = (uu___126_1525.unfold_only);
            unfold_fully = (uu___126_1525.unfold_fully);
            unfold_attr = (uu___126_1525.unfold_attr);
            unfold_tac = (uu___126_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1525.pure_subterms_within_computations);
            simplify = (uu___126_1525.simplify);
            erase_universes = (uu___126_1525.erase_universes);
            allow_unbound_universes = (uu___126_1525.allow_unbound_universes);
            reify_ = (uu___126_1525.reify_);
            compress_uvars = (uu___126_1525.compress_uvars);
            no_full_norm = (uu___126_1525.no_full_norm);
            check_no_uvars = (uu___126_1525.check_no_uvars);
            unmeta = (uu___126_1525.unmeta);
            unascribe = (uu___126_1525.unascribe);
            in_full_norm_request = (uu___126_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___127_1526 = fs  in
          {
            beta = false;
            iota = (uu___127_1526.iota);
            zeta = (uu___127_1526.zeta);
            weak = (uu___127_1526.weak);
            hnf = (uu___127_1526.hnf);
            primops = (uu___127_1526.primops);
            do_not_unfold_pure_lets = (uu___127_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___127_1526.unfold_until);
            unfold_only = (uu___127_1526.unfold_only);
            unfold_fully = (uu___127_1526.unfold_fully);
            unfold_attr = (uu___127_1526.unfold_attr);
            unfold_tac = (uu___127_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___127_1526.pure_subterms_within_computations);
            simplify = (uu___127_1526.simplify);
            erase_universes = (uu___127_1526.erase_universes);
            allow_unbound_universes = (uu___127_1526.allow_unbound_universes);
            reify_ = (uu___127_1526.reify_);
            compress_uvars = (uu___127_1526.compress_uvars);
            no_full_norm = (uu___127_1526.no_full_norm);
            check_no_uvars = (uu___127_1526.check_no_uvars);
            unmeta = (uu___127_1526.unmeta);
            unascribe = (uu___127_1526.unascribe);
            in_full_norm_request = (uu___127_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___127_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___128_1527 = fs  in
          {
            beta = (uu___128_1527.beta);
            iota = false;
            zeta = (uu___128_1527.zeta);
            weak = (uu___128_1527.weak);
            hnf = (uu___128_1527.hnf);
            primops = (uu___128_1527.primops);
            do_not_unfold_pure_lets = (uu___128_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___128_1527.unfold_until);
            unfold_only = (uu___128_1527.unfold_only);
            unfold_fully = (uu___128_1527.unfold_fully);
            unfold_attr = (uu___128_1527.unfold_attr);
            unfold_tac = (uu___128_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_1527.pure_subterms_within_computations);
            simplify = (uu___128_1527.simplify);
            erase_universes = (uu___128_1527.erase_universes);
            allow_unbound_universes = (uu___128_1527.allow_unbound_universes);
            reify_ = (uu___128_1527.reify_);
            compress_uvars = (uu___128_1527.compress_uvars);
            no_full_norm = (uu___128_1527.no_full_norm);
            check_no_uvars = (uu___128_1527.check_no_uvars);
            unmeta = (uu___128_1527.unmeta);
            unascribe = (uu___128_1527.unascribe);
            in_full_norm_request = (uu___128_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___129_1528 = fs  in
          {
            beta = (uu___129_1528.beta);
            iota = (uu___129_1528.iota);
            zeta = false;
            weak = (uu___129_1528.weak);
            hnf = (uu___129_1528.hnf);
            primops = (uu___129_1528.primops);
            do_not_unfold_pure_lets = (uu___129_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___129_1528.unfold_until);
            unfold_only = (uu___129_1528.unfold_only);
            unfold_fully = (uu___129_1528.unfold_fully);
            unfold_attr = (uu___129_1528.unfold_attr);
            unfold_tac = (uu___129_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1528.pure_subterms_within_computations);
            simplify = (uu___129_1528.simplify);
            erase_universes = (uu___129_1528.erase_universes);
            allow_unbound_universes = (uu___129_1528.allow_unbound_universes);
            reify_ = (uu___129_1528.reify_);
            compress_uvars = (uu___129_1528.compress_uvars);
            no_full_norm = (uu___129_1528.no_full_norm);
            check_no_uvars = (uu___129_1528.check_no_uvars);
            unmeta = (uu___129_1528.unmeta);
            unascribe = (uu___129_1528.unascribe);
            in_full_norm_request = (uu___129_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___130_1530 = fs  in
          {
            beta = (uu___130_1530.beta);
            iota = (uu___130_1530.iota);
            zeta = (uu___130_1530.zeta);
            weak = true;
            hnf = (uu___130_1530.hnf);
            primops = (uu___130_1530.primops);
            do_not_unfold_pure_lets = (uu___130_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___130_1530.unfold_until);
            unfold_only = (uu___130_1530.unfold_only);
            unfold_fully = (uu___130_1530.unfold_fully);
            unfold_attr = (uu___130_1530.unfold_attr);
            unfold_tac = (uu___130_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___130_1530.pure_subterms_within_computations);
            simplify = (uu___130_1530.simplify);
            erase_universes = (uu___130_1530.erase_universes);
            allow_unbound_universes = (uu___130_1530.allow_unbound_universes);
            reify_ = (uu___130_1530.reify_);
            compress_uvars = (uu___130_1530.compress_uvars);
            no_full_norm = (uu___130_1530.no_full_norm);
            check_no_uvars = (uu___130_1530.check_no_uvars);
            unmeta = (uu___130_1530.unmeta);
            unascribe = (uu___130_1530.unascribe);
            in_full_norm_request = (uu___130_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___130_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___131_1531 = fs  in
          {
            beta = (uu___131_1531.beta);
            iota = (uu___131_1531.iota);
            zeta = (uu___131_1531.zeta);
            weak = (uu___131_1531.weak);
            hnf = true;
            primops = (uu___131_1531.primops);
            do_not_unfold_pure_lets = (uu___131_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___131_1531.unfold_until);
            unfold_only = (uu___131_1531.unfold_only);
            unfold_fully = (uu___131_1531.unfold_fully);
            unfold_attr = (uu___131_1531.unfold_attr);
            unfold_tac = (uu___131_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_1531.pure_subterms_within_computations);
            simplify = (uu___131_1531.simplify);
            erase_universes = (uu___131_1531.erase_universes);
            allow_unbound_universes = (uu___131_1531.allow_unbound_universes);
            reify_ = (uu___131_1531.reify_);
            compress_uvars = (uu___131_1531.compress_uvars);
            no_full_norm = (uu___131_1531.no_full_norm);
            check_no_uvars = (uu___131_1531.check_no_uvars);
            unmeta = (uu___131_1531.unmeta);
            unascribe = (uu___131_1531.unascribe);
            in_full_norm_request = (uu___131_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___132_1532 = fs  in
          {
            beta = (uu___132_1532.beta);
            iota = (uu___132_1532.iota);
            zeta = (uu___132_1532.zeta);
            weak = (uu___132_1532.weak);
            hnf = (uu___132_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___132_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___132_1532.unfold_until);
            unfold_only = (uu___132_1532.unfold_only);
            unfold_fully = (uu___132_1532.unfold_fully);
            unfold_attr = (uu___132_1532.unfold_attr);
            unfold_tac = (uu___132_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_1532.pure_subterms_within_computations);
            simplify = (uu___132_1532.simplify);
            erase_universes = (uu___132_1532.erase_universes);
            allow_unbound_universes = (uu___132_1532.allow_unbound_universes);
            reify_ = (uu___132_1532.reify_);
            compress_uvars = (uu___132_1532.compress_uvars);
            no_full_norm = (uu___132_1532.no_full_norm);
            check_no_uvars = (uu___132_1532.check_no_uvars);
            unmeta = (uu___132_1532.unmeta);
            unascribe = (uu___132_1532.unascribe);
            in_full_norm_request = (uu___132_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___133_1533 = fs  in
          {
            beta = (uu___133_1533.beta);
            iota = (uu___133_1533.iota);
            zeta = (uu___133_1533.zeta);
            weak = (uu___133_1533.weak);
            hnf = (uu___133_1533.hnf);
            primops = (uu___133_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___133_1533.unfold_until);
            unfold_only = (uu___133_1533.unfold_only);
            unfold_fully = (uu___133_1533.unfold_fully);
            unfold_attr = (uu___133_1533.unfold_attr);
            unfold_tac = (uu___133_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_1533.pure_subterms_within_computations);
            simplify = (uu___133_1533.simplify);
            erase_universes = (uu___133_1533.erase_universes);
            allow_unbound_universes = (uu___133_1533.allow_unbound_universes);
            reify_ = (uu___133_1533.reify_);
            compress_uvars = (uu___133_1533.compress_uvars);
            no_full_norm = (uu___133_1533.no_full_norm);
            check_no_uvars = (uu___133_1533.check_no_uvars);
            unmeta = (uu___133_1533.unmeta);
            unascribe = (uu___133_1533.unascribe);
            in_full_norm_request = (uu___133_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___134_1535 = fs  in
          {
            beta = (uu___134_1535.beta);
            iota = (uu___134_1535.iota);
            zeta = (uu___134_1535.zeta);
            weak = (uu___134_1535.weak);
            hnf = (uu___134_1535.hnf);
            primops = (uu___134_1535.primops);
            do_not_unfold_pure_lets = (uu___134_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___134_1535.unfold_only);
            unfold_fully = (uu___134_1535.unfold_fully);
            unfold_attr = (uu___134_1535.unfold_attr);
            unfold_tac = (uu___134_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_1535.pure_subterms_within_computations);
            simplify = (uu___134_1535.simplify);
            erase_universes = (uu___134_1535.erase_universes);
            allow_unbound_universes = (uu___134_1535.allow_unbound_universes);
            reify_ = (uu___134_1535.reify_);
            compress_uvars = (uu___134_1535.compress_uvars);
            no_full_norm = (uu___134_1535.no_full_norm);
            check_no_uvars = (uu___134_1535.check_no_uvars);
            unmeta = (uu___134_1535.unmeta);
            unascribe = (uu___134_1535.unascribe);
            in_full_norm_request = (uu___134_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___135_1539 = fs  in
          {
            beta = (uu___135_1539.beta);
            iota = (uu___135_1539.iota);
            zeta = (uu___135_1539.zeta);
            weak = (uu___135_1539.weak);
            hnf = (uu___135_1539.hnf);
            primops = (uu___135_1539.primops);
            do_not_unfold_pure_lets = (uu___135_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___135_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___135_1539.unfold_fully);
            unfold_attr = (uu___135_1539.unfold_attr);
            unfold_tac = (uu___135_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___135_1539.pure_subterms_within_computations);
            simplify = (uu___135_1539.simplify);
            erase_universes = (uu___135_1539.erase_universes);
            allow_unbound_universes = (uu___135_1539.allow_unbound_universes);
            reify_ = (uu___135_1539.reify_);
            compress_uvars = (uu___135_1539.compress_uvars);
            no_full_norm = (uu___135_1539.no_full_norm);
            check_no_uvars = (uu___135_1539.check_no_uvars);
            unmeta = (uu___135_1539.unmeta);
            unascribe = (uu___135_1539.unascribe);
            in_full_norm_request = (uu___135_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___135_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___136_1545 = fs  in
          {
            beta = (uu___136_1545.beta);
            iota = (uu___136_1545.iota);
            zeta = (uu___136_1545.zeta);
            weak = (uu___136_1545.weak);
            hnf = (uu___136_1545.hnf);
            primops = (uu___136_1545.primops);
            do_not_unfold_pure_lets = (uu___136_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___136_1545.unfold_until);
            unfold_only = (uu___136_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___136_1545.unfold_attr);
            unfold_tac = (uu___136_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_1545.pure_subterms_within_computations);
            simplify = (uu___136_1545.simplify);
            erase_universes = (uu___136_1545.erase_universes);
            allow_unbound_universes = (uu___136_1545.allow_unbound_universes);
            reify_ = (uu___136_1545.reify_);
            compress_uvars = (uu___136_1545.compress_uvars);
            no_full_norm = (uu___136_1545.no_full_norm);
            check_no_uvars = (uu___136_1545.check_no_uvars);
            unmeta = (uu___136_1545.unmeta);
            unascribe = (uu___136_1545.unascribe);
            in_full_norm_request = (uu___136_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___137_1549 = fs  in
          {
            beta = (uu___137_1549.beta);
            iota = (uu___137_1549.iota);
            zeta = (uu___137_1549.zeta);
            weak = (uu___137_1549.weak);
            hnf = (uu___137_1549.hnf);
            primops = (uu___137_1549.primops);
            do_not_unfold_pure_lets = (uu___137_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___137_1549.unfold_until);
            unfold_only = (uu___137_1549.unfold_only);
            unfold_fully = (uu___137_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___137_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_1549.pure_subterms_within_computations);
            simplify = (uu___137_1549.simplify);
            erase_universes = (uu___137_1549.erase_universes);
            allow_unbound_universes = (uu___137_1549.allow_unbound_universes);
            reify_ = (uu___137_1549.reify_);
            compress_uvars = (uu___137_1549.compress_uvars);
            no_full_norm = (uu___137_1549.no_full_norm);
            check_no_uvars = (uu___137_1549.check_no_uvars);
            unmeta = (uu___137_1549.unmeta);
            unascribe = (uu___137_1549.unascribe);
            in_full_norm_request = (uu___137_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___138_1550 = fs  in
          {
            beta = (uu___138_1550.beta);
            iota = (uu___138_1550.iota);
            zeta = (uu___138_1550.zeta);
            weak = (uu___138_1550.weak);
            hnf = (uu___138_1550.hnf);
            primops = (uu___138_1550.primops);
            do_not_unfold_pure_lets = (uu___138_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___138_1550.unfold_until);
            unfold_only = (uu___138_1550.unfold_only);
            unfold_fully = (uu___138_1550.unfold_fully);
            unfold_attr = (uu___138_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___138_1550.pure_subterms_within_computations);
            simplify = (uu___138_1550.simplify);
            erase_universes = (uu___138_1550.erase_universes);
            allow_unbound_universes = (uu___138_1550.allow_unbound_universes);
            reify_ = (uu___138_1550.reify_);
            compress_uvars = (uu___138_1550.compress_uvars);
            no_full_norm = (uu___138_1550.no_full_norm);
            check_no_uvars = (uu___138_1550.check_no_uvars);
            unmeta = (uu___138_1550.unmeta);
            unascribe = (uu___138_1550.unascribe);
            in_full_norm_request = (uu___138_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___139_1551 = fs  in
          {
            beta = (uu___139_1551.beta);
            iota = (uu___139_1551.iota);
            zeta = (uu___139_1551.zeta);
            weak = (uu___139_1551.weak);
            hnf = (uu___139_1551.hnf);
            primops = (uu___139_1551.primops);
            do_not_unfold_pure_lets = (uu___139_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___139_1551.unfold_until);
            unfold_only = (uu___139_1551.unfold_only);
            unfold_fully = (uu___139_1551.unfold_fully);
            unfold_attr = (uu___139_1551.unfold_attr);
            unfold_tac = (uu___139_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___139_1551.simplify);
            erase_universes = (uu___139_1551.erase_universes);
            allow_unbound_universes = (uu___139_1551.allow_unbound_universes);
            reify_ = (uu___139_1551.reify_);
            compress_uvars = (uu___139_1551.compress_uvars);
            no_full_norm = (uu___139_1551.no_full_norm);
            check_no_uvars = (uu___139_1551.check_no_uvars);
            unmeta = (uu___139_1551.unmeta);
            unascribe = (uu___139_1551.unascribe);
            in_full_norm_request = (uu___139_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___139_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___140_1552 = fs  in
          {
            beta = (uu___140_1552.beta);
            iota = (uu___140_1552.iota);
            zeta = (uu___140_1552.zeta);
            weak = (uu___140_1552.weak);
            hnf = (uu___140_1552.hnf);
            primops = (uu___140_1552.primops);
            do_not_unfold_pure_lets = (uu___140_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___140_1552.unfold_until);
            unfold_only = (uu___140_1552.unfold_only);
            unfold_fully = (uu___140_1552.unfold_fully);
            unfold_attr = (uu___140_1552.unfold_attr);
            unfold_tac = (uu___140_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___140_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___140_1552.erase_universes);
            allow_unbound_universes = (uu___140_1552.allow_unbound_universes);
            reify_ = (uu___140_1552.reify_);
            compress_uvars = (uu___140_1552.compress_uvars);
            no_full_norm = (uu___140_1552.no_full_norm);
            check_no_uvars = (uu___140_1552.check_no_uvars);
            unmeta = (uu___140_1552.unmeta);
            unascribe = (uu___140_1552.unascribe);
            in_full_norm_request = (uu___140_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___141_1553 = fs  in
          {
            beta = (uu___141_1553.beta);
            iota = (uu___141_1553.iota);
            zeta = (uu___141_1553.zeta);
            weak = (uu___141_1553.weak);
            hnf = (uu___141_1553.hnf);
            primops = (uu___141_1553.primops);
            do_not_unfold_pure_lets = (uu___141_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___141_1553.unfold_until);
            unfold_only = (uu___141_1553.unfold_only);
            unfold_fully = (uu___141_1553.unfold_fully);
            unfold_attr = (uu___141_1553.unfold_attr);
            unfold_tac = (uu___141_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___141_1553.pure_subterms_within_computations);
            simplify = (uu___141_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___141_1553.allow_unbound_universes);
            reify_ = (uu___141_1553.reify_);
            compress_uvars = (uu___141_1553.compress_uvars);
            no_full_norm = (uu___141_1553.no_full_norm);
            check_no_uvars = (uu___141_1553.check_no_uvars);
            unmeta = (uu___141_1553.unmeta);
            unascribe = (uu___141_1553.unascribe);
            in_full_norm_request = (uu___141_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___142_1554 = fs  in
          {
            beta = (uu___142_1554.beta);
            iota = (uu___142_1554.iota);
            zeta = (uu___142_1554.zeta);
            weak = (uu___142_1554.weak);
            hnf = (uu___142_1554.hnf);
            primops = (uu___142_1554.primops);
            do_not_unfold_pure_lets = (uu___142_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1554.unfold_until);
            unfold_only = (uu___142_1554.unfold_only);
            unfold_fully = (uu___142_1554.unfold_fully);
            unfold_attr = (uu___142_1554.unfold_attr);
            unfold_tac = (uu___142_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1554.pure_subterms_within_computations);
            simplify = (uu___142_1554.simplify);
            erase_universes = (uu___142_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___142_1554.reify_);
            compress_uvars = (uu___142_1554.compress_uvars);
            no_full_norm = (uu___142_1554.no_full_norm);
            check_no_uvars = (uu___142_1554.check_no_uvars);
            unmeta = (uu___142_1554.unmeta);
            unascribe = (uu___142_1554.unascribe);
            in_full_norm_request = (uu___142_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___143_1555 = fs  in
          {
            beta = (uu___143_1555.beta);
            iota = (uu___143_1555.iota);
            zeta = (uu___143_1555.zeta);
            weak = (uu___143_1555.weak);
            hnf = (uu___143_1555.hnf);
            primops = (uu___143_1555.primops);
            do_not_unfold_pure_lets = (uu___143_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___143_1555.unfold_until);
            unfold_only = (uu___143_1555.unfold_only);
            unfold_fully = (uu___143_1555.unfold_fully);
            unfold_attr = (uu___143_1555.unfold_attr);
            unfold_tac = (uu___143_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___143_1555.pure_subterms_within_computations);
            simplify = (uu___143_1555.simplify);
            erase_universes = (uu___143_1555.erase_universes);
            allow_unbound_universes = (uu___143_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___143_1555.compress_uvars);
            no_full_norm = (uu___143_1555.no_full_norm);
            check_no_uvars = (uu___143_1555.check_no_uvars);
            unmeta = (uu___143_1555.unmeta);
            unascribe = (uu___143_1555.unascribe);
            in_full_norm_request = (uu___143_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___143_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___144_1556 = fs  in
          {
            beta = (uu___144_1556.beta);
            iota = (uu___144_1556.iota);
            zeta = (uu___144_1556.zeta);
            weak = (uu___144_1556.weak);
            hnf = (uu___144_1556.hnf);
            primops = (uu___144_1556.primops);
            do_not_unfold_pure_lets = (uu___144_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___144_1556.unfold_until);
            unfold_only = (uu___144_1556.unfold_only);
            unfold_fully = (uu___144_1556.unfold_fully);
            unfold_attr = (uu___144_1556.unfold_attr);
            unfold_tac = (uu___144_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_1556.pure_subterms_within_computations);
            simplify = (uu___144_1556.simplify);
            erase_universes = (uu___144_1556.erase_universes);
            allow_unbound_universes = (uu___144_1556.allow_unbound_universes);
            reify_ = (uu___144_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___144_1556.no_full_norm);
            check_no_uvars = (uu___144_1556.check_no_uvars);
            unmeta = (uu___144_1556.unmeta);
            unascribe = (uu___144_1556.unascribe);
            in_full_norm_request = (uu___144_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___145_1557 = fs  in
          {
            beta = (uu___145_1557.beta);
            iota = (uu___145_1557.iota);
            zeta = (uu___145_1557.zeta);
            weak = (uu___145_1557.weak);
            hnf = (uu___145_1557.hnf);
            primops = (uu___145_1557.primops);
            do_not_unfold_pure_lets = (uu___145_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___145_1557.unfold_until);
            unfold_only = (uu___145_1557.unfold_only);
            unfold_fully = (uu___145_1557.unfold_fully);
            unfold_attr = (uu___145_1557.unfold_attr);
            unfold_tac = (uu___145_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___145_1557.pure_subterms_within_computations);
            simplify = (uu___145_1557.simplify);
            erase_universes = (uu___145_1557.erase_universes);
            allow_unbound_universes = (uu___145_1557.allow_unbound_universes);
            reify_ = (uu___145_1557.reify_);
            compress_uvars = (uu___145_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___145_1557.check_no_uvars);
            unmeta = (uu___145_1557.unmeta);
            unascribe = (uu___145_1557.unascribe);
            in_full_norm_request = (uu___145_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___145_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___146_1558 = fs  in
          {
            beta = (uu___146_1558.beta);
            iota = (uu___146_1558.iota);
            zeta = (uu___146_1558.zeta);
            weak = (uu___146_1558.weak);
            hnf = (uu___146_1558.hnf);
            primops = (uu___146_1558.primops);
            do_not_unfold_pure_lets = (uu___146_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___146_1558.unfold_until);
            unfold_only = (uu___146_1558.unfold_only);
            unfold_fully = (uu___146_1558.unfold_fully);
            unfold_attr = (uu___146_1558.unfold_attr);
            unfold_tac = (uu___146_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_1558.pure_subterms_within_computations);
            simplify = (uu___146_1558.simplify);
            erase_universes = (uu___146_1558.erase_universes);
            allow_unbound_universes = (uu___146_1558.allow_unbound_universes);
            reify_ = (uu___146_1558.reify_);
            compress_uvars = (uu___146_1558.compress_uvars);
            no_full_norm = (uu___146_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___146_1558.unmeta);
            unascribe = (uu___146_1558.unascribe);
            in_full_norm_request = (uu___146_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___147_1559 = fs  in
          {
            beta = (uu___147_1559.beta);
            iota = (uu___147_1559.iota);
            zeta = (uu___147_1559.zeta);
            weak = (uu___147_1559.weak);
            hnf = (uu___147_1559.hnf);
            primops = (uu___147_1559.primops);
            do_not_unfold_pure_lets = (uu___147_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___147_1559.unfold_until);
            unfold_only = (uu___147_1559.unfold_only);
            unfold_fully = (uu___147_1559.unfold_fully);
            unfold_attr = (uu___147_1559.unfold_attr);
            unfold_tac = (uu___147_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___147_1559.pure_subterms_within_computations);
            simplify = (uu___147_1559.simplify);
            erase_universes = (uu___147_1559.erase_universes);
            allow_unbound_universes = (uu___147_1559.allow_unbound_universes);
            reify_ = (uu___147_1559.reify_);
            compress_uvars = (uu___147_1559.compress_uvars);
            no_full_norm = (uu___147_1559.no_full_norm);
            check_no_uvars = (uu___147_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___147_1559.unascribe);
            in_full_norm_request = (uu___147_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___147_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___148_1560 = fs  in
          {
            beta = (uu___148_1560.beta);
            iota = (uu___148_1560.iota);
            zeta = (uu___148_1560.zeta);
            weak = (uu___148_1560.weak);
            hnf = (uu___148_1560.hnf);
            primops = (uu___148_1560.primops);
            do_not_unfold_pure_lets = (uu___148_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___148_1560.unfold_until);
            unfold_only = (uu___148_1560.unfold_only);
            unfold_fully = (uu___148_1560.unfold_fully);
            unfold_attr = (uu___148_1560.unfold_attr);
            unfold_tac = (uu___148_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___148_1560.pure_subterms_within_computations);
            simplify = (uu___148_1560.simplify);
            erase_universes = (uu___148_1560.erase_universes);
            allow_unbound_universes = (uu___148_1560.allow_unbound_universes);
            reify_ = (uu___148_1560.reify_);
            compress_uvars = (uu___148_1560.compress_uvars);
            no_full_norm = (uu___148_1560.no_full_norm);
            check_no_uvars = (uu___148_1560.check_no_uvars);
            unmeta = (uu___148_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___148_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___148_1560.weakly_reduce_scrutinee)
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
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
    }[@@deriving show]
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
  | Dummy [@@deriving show]
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
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
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
  print_normalized: Prims.bool }[@@deriving show]
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
  normalize_pure_lets: Prims.bool }[@@deriving show]
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
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
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
type stack = stack_elt Prims.list[@@deriving show]
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
  fun uu___107_3222  ->
    match uu___107_3222 with
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
  fun uu___108_3284  ->
    match uu___108_3284 with
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
  fun uu___109_3404  ->
    match uu___109_3404 with | [] -> true | uu____3407 -> false
  
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
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
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
                | FStar_Syntax_Syntax.Tm_uvar uu____3929 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3935 ->
                           let uu____3936 =
                             let uu____3937 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3938 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3937 uu____3938
                              in
                           failwith uu____3936
                       | uu____3941 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3947 =
                        let uu____3948 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3948  in
                      mk uu____3947 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3956 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3956  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3958 = lookup_bvar env x  in
                    (match uu____3958 with
                     | Univ uu____3961 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___153_3965 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___153_3965.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___153_3965.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3971,uu____3972) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4057  ->
                              fun stack1  ->
                                match uu____4057 with
                                | (a,aq) ->
                                    let uu____4069 =
                                      let uu____4070 =
                                        let uu____4077 =
                                          let uu____4078 =
                                            let uu____4109 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4109, false)  in
                                          Clos uu____4078  in
                                        (uu____4077, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4070  in
                                    uu____4069 :: stack1) args)
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
                    let uu____4285 = close_binders cfg env bs  in
                    (match uu____4285 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4332 =
                      let uu____4343 =
                        let uu____4350 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4350]  in
                      close_binders cfg env uu____4343  in
                    (match uu____4332 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4373 =
                             let uu____4374 =
                               let uu____4381 =
                                 let uu____4382 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4382
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4381, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4374  in
                           mk uu____4373 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4473 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4473
                      | FStar_Util.Inr c ->
                          let uu____4487 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4487
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4506 =
                        let uu____4507 =
                          let uu____4534 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4534, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4507  in
                      mk uu____4506 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4580 =
                            let uu____4581 =
                              let uu____4588 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4588, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4581  in
                          mk uu____4580 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4640  -> dummy :: env1) env
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
                    let uu____4661 =
                      let uu____4672 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4672
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4691 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___154_4707 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_4707.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_4707.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4691))
                       in
                    (match uu____4661 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___155_4725 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___155_4725.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___155_4725.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___155_4725.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___155_4725.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4739,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4802  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4819 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4819
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4831  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4855 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4855
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___156_4863 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___156_4863.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___156_4863.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___157_4864 = lb  in
                      let uu____4865 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___157_4864.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___157_4864.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4865;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___157_4864.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___157_4864.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4897  -> fun env1  -> dummy :: env1)
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
            (fun uu____4986  ->
               let uu____4987 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4988 = env_to_string env  in
               let uu____4989 = stack_to_string stack  in
               let uu____4990 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4987 uu____4988 uu____4989 uu____4990);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4995,uu____4996),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5073 = close_binders cfg env' bs  in
               (match uu____5073 with
                | (bs1,uu____5087) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5103 =
                      let uu___158_5106 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___158_5106.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___158_5106.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5103)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5162 =
                 match uu____5162 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5277 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5306 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5390  ->
                                     fun uu____5391  ->
                                       match (uu____5390, uu____5391) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5530 = norm_pat env4 p1
                                              in
                                           (match uu____5530 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5306 with
                            | (pats1,env4) ->
                                ((let uu___159_5692 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___159_5692.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___160_5711 = x  in
                             let uu____5712 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_5711.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_5711.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5712
                             }  in
                           ((let uu___161_5726 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___161_5726.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___162_5737 = x  in
                             let uu____5738 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_5737.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_5737.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5738
                             }  in
                           ((let uu___163_5752 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___163_5752.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___164_5768 = x  in
                             let uu____5769 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___164_5768.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___164_5768.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5769
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___165_5786 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___165_5786.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5791 = norm_pat env2 pat  in
                     (match uu____5791 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5860 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5860
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5879 =
                   let uu____5880 =
                     let uu____5903 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5903)  in
                   FStar_Syntax_Syntax.Tm_match uu____5880  in
                 mk uu____5879 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6016 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6105  ->
                                       match uu____6105 with
                                       | (a,q) ->
                                           let uu____6124 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6124, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6016
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6135 =
                       let uu____6142 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6142)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6135
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6154 =
                       let uu____6163 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6163)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6154
                 | uu____6168 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6174 -> failwith "Impossible: unexpected stack element")

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
        let uu____6188 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6261  ->
                  fun uu____6262  ->
                    match (uu____6261, uu____6262) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___166_6380 = b  in
                          let uu____6381 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___166_6380.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___166_6380.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6381
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6188 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6498 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6511 = inline_closure_env cfg env [] t  in
                 let uu____6512 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6511 uu____6512
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6525 = inline_closure_env cfg env [] t  in
                 let uu____6526 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6525 uu____6526
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6570  ->
                           match uu____6570 with
                           | (a,q) ->
                               let uu____6583 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6583, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___110_6598  ->
                           match uu___110_6598 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6602 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6602
                           | f -> f))
                    in
                 let uu____6606 =
                   let uu___167_6607 = c1  in
                   let uu____6608 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6608;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___167_6607.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6606)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___111_6618  ->
            match uu___111_6618 with
            | FStar_Syntax_Syntax.DECREASES uu____6619 -> false
            | uu____6622 -> true))

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
                   (fun uu___112_6640  ->
                      match uu___112_6640 with
                      | FStar_Syntax_Syntax.DECREASES uu____6641 -> false
                      | uu____6644 -> true))
               in
            let rc1 =
              let uu___168_6646 = rc  in
              let uu____6647 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___168_6646.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6647;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6656 -> lopt

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
    let uu____6761 =
      let uu____6770 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6770  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6761  in
  let arg_as_bounded_int uu____6796 =
    match uu____6796 with
    | (a,uu____6808) ->
        let uu____6815 =
          let uu____6816 = FStar_Syntax_Subst.compress a  in
          uu____6816.FStar_Syntax_Syntax.n  in
        (match uu____6815 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6826;
                FStar_Syntax_Syntax.vars = uu____6827;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6829;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6830;_},uu____6831)::[])
             when
             let uu____6870 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6870 "int_to_t" ->
             let uu____6871 =
               let uu____6876 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6876)  in
             FStar_Pervasives_Native.Some uu____6871
         | uu____6881 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6929 = f a  in FStar_Pervasives_Native.Some uu____6929
    | uu____6930 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6986 = f a0 a1  in FStar_Pervasives_Native.Some uu____6986
    | uu____6987 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7045 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7045  in
  let binary_op as_a f res args =
    let uu____7116 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7116  in
  let as_primitive_step is_strong uu____7153 =
    match uu____7153 with
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
           let uu____7213 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7213)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7249 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7249)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7278 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7278)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7314 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7314)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7350 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7350)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7482 =
          let uu____7491 = as_a a  in
          let uu____7494 = as_b b  in (uu____7491, uu____7494)  in
        (match uu____7482 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7509 =
               let uu____7510 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7510  in
             FStar_Pervasives_Native.Some uu____7509
         | uu____7511 -> FStar_Pervasives_Native.None)
    | uu____7520 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7540 =
        let uu____7541 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7541  in
      mk uu____7540 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7553 =
      let uu____7556 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7556  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7553  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7598 =
      let uu____7599 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7599  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7598
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7663 = arg_as_string a1  in
        (match uu____7663 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7669 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7669 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7682 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7682
              | uu____7683 -> FStar_Pervasives_Native.None)
         | uu____7688 -> FStar_Pervasives_Native.None)
    | uu____7691 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7711 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7711
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7748 =
          let uu____7769 = arg_as_string fn  in
          let uu____7772 = arg_as_int from_line  in
          let uu____7775 = arg_as_int from_col  in
          let uu____7778 = arg_as_int to_line  in
          let uu____7781 = arg_as_int to_col  in
          (uu____7769, uu____7772, uu____7775, uu____7778, uu____7781)  in
        (match uu____7748 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7812 =
                 let uu____7813 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7814 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7813 uu____7814  in
               let uu____7815 =
                 let uu____7816 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7817 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7816 uu____7817  in
               FStar_Range.mk_range fn1 uu____7812 uu____7815  in
             let uu____7818 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7818
         | uu____7819 -> FStar_Pervasives_Native.None)
    | uu____7840 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7873)::(a1,uu____7875)::(a2,uu____7877)::[] ->
        let uu____7914 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7914 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7919 -> FStar_Pervasives_Native.None)
    | uu____7920 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7951)::[] ->
        let uu____7960 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7960 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7966 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7966
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7967 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7993 =
      let uu____8010 =
        let uu____8027 =
          let uu____8044 =
            let uu____8061 =
              let uu____8078 =
                let uu____8095 =
                  let uu____8112 =
                    let uu____8129 =
                      let uu____8146 =
                        let uu____8163 =
                          let uu____8180 =
                            let uu____8197 =
                              let uu____8214 =
                                let uu____8231 =
                                  let uu____8248 =
                                    let uu____8265 =
                                      let uu____8282 =
                                        let uu____8299 =
                                          let uu____8316 =
                                            let uu____8333 =
                                              let uu____8350 =
                                                let uu____8365 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8365,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8374 =
                                                let uu____8391 =
                                                  let uu____8406 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8406,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8419 =
                                                  let uu____8436 =
                                                    let uu____8451 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8451,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8460 =
                                                    let uu____8477 =
                                                      let uu____8492 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8492,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8477]  in
                                                  uu____8436 :: uu____8460
                                                   in
                                                uu____8391 :: uu____8419  in
                                              uu____8350 :: uu____8374  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8333
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8316
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8299
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8282
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8265
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8712 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8712 y)))
                                    :: uu____8248
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8231
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8214
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8197
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8180
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8163
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8146
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8907 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8907)))
                      :: uu____8129
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8937 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8937)))
                    :: uu____8112
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8967 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8967)))
                  :: uu____8095
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8997 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8997)))
                :: uu____8078
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8061
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8044
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8027
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8010
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7993
     in
  let weak_ops =
    let uu____9152 =
      let uu____9167 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9167, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9152]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9247 =
        let uu____9252 =
          let uu____9253 = FStar_Syntax_Syntax.as_arg c  in [uu____9253]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9252  in
      uu____9247 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9327 =
                let uu____9342 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9342, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9364  ->
                          fun uu____9365  ->
                            match (uu____9364, uu____9365) with
                            | ((int_to_t1,x),(uu____9384,y)) ->
                                let uu____9394 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9394)))
                 in
              let uu____9395 =
                let uu____9412 =
                  let uu____9427 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9427, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9449  ->
                            fun uu____9450  ->
                              match (uu____9449, uu____9450) with
                              | ((int_to_t1,x),(uu____9469,y)) ->
                                  let uu____9479 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9479)))
                   in
                let uu____9480 =
                  let uu____9497 =
                    let uu____9512 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9512, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9534  ->
                              fun uu____9535  ->
                                match (uu____9534, uu____9535) with
                                | ((int_to_t1,x),(uu____9554,y)) ->
                                    let uu____9564 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9564)))
                     in
                  let uu____9565 =
                    let uu____9582 =
                      let uu____9597 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9597, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9615  ->
                                match uu____9615 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9582]  in
                  uu____9497 :: uu____9565  in
                uu____9412 :: uu____9480  in
              uu____9327 :: uu____9395))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9745 =
                let uu____9760 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9760, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9782  ->
                          fun uu____9783  ->
                            match (uu____9782, uu____9783) with
                            | ((int_to_t1,x),(uu____9802,y)) ->
                                let uu____9812 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9812)))
                 in
              let uu____9813 =
                let uu____9830 =
                  let uu____9845 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9845, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9867  ->
                            fun uu____9868  ->
                              match (uu____9867, uu____9868) with
                              | ((int_to_t1,x),(uu____9887,y)) ->
                                  let uu____9897 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9897)))
                   in
                [uu____9830]  in
              uu____9745 :: uu____9813))
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
    | (_typ,uu____10027)::(a1,uu____10029)::(a2,uu____10031)::[] ->
        let uu____10068 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10068 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10072 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10072.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10072.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10074 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10074.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10074.FStar_Syntax_Syntax.vars)
                })
         | uu____10075 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10077)::uu____10078::(a1,uu____10080)::(a2,uu____10082)::[]
        ->
        let uu____10131 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10131 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___169_10135 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___169_10135.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___169_10135.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___170_10137 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___170_10137.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___170_10137.FStar_Syntax_Syntax.vars)
                })
         | uu____10138 -> FStar_Pervasives_Native.None)
    | uu____10139 -> failwith "Unexpected number of arguments"  in
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
    let uu____10193 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10193 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10245 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10245) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10307  ->
           fun subst1  ->
             match uu____10307 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10348,uu____10349)) ->
                      let uu____10408 = b  in
                      (match uu____10408 with
                       | (bv,uu____10416) ->
                           let uu____10417 =
                             let uu____10418 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10418  in
                           if uu____10417
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10423 = unembed_binder term1  in
                              match uu____10423 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10430 =
                                      let uu___171_10431 = bv  in
                                      let uu____10432 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___171_10431.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___171_10431.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10432
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10430
                                     in
                                  let b_for_x =
                                    let uu____10436 =
                                      let uu____10443 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10443)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10436  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___113_10457  ->
                                         match uu___113_10457 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10458,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10460;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10461;_})
                                             ->
                                             let uu____10466 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10466
                                         | uu____10467 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10468 -> subst1)) env []
  
let reduce_primops :
  'Auu____10491 'Auu____10492 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10491) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10492 ->
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
            (let uu____10540 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10540 with
             | (head1,args) ->
                 let uu____10579 =
                   let uu____10580 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10580.FStar_Syntax_Syntax.n  in
                 (match uu____10579 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10586 = find_prim_step cfg fv  in
                      (match uu____10586 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10612  ->
                                   let uu____10613 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10614 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10621 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10613 uu____10614 uu____10621);
                              tm)
                           else
                             (let uu____10623 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10623 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10737  ->
                                        let uu____10738 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10738);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10741  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10743 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10743 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10751  ->
                                              let uu____10752 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10752);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10758  ->
                                              let uu____10759 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10760 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10759 uu____10760);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10761 ->
                           (log_primops cfg
                              (fun uu____10765  ->
                                 let uu____10766 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10766);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10770  ->
                            let uu____10771 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10771);
                       (match args with
                        | (a1,uu____10775)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10792 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10804  ->
                            let uu____10805 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10805);
                       (match args with
                        | (t,uu____10809)::(r,uu____10811)::[] ->
                            let uu____10838 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10838 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___172_10844 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___172_10844.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___172_10844.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10847 -> tm))
                  | uu____10856 -> tm))
  
let reduce_equality :
  'Auu____10867 'Auu____10868 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10867) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10868 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___173_10914 = cfg  in
         {
           steps =
             (let uu___174_10917 = default_steps  in
              {
                beta = (uu___174_10917.beta);
                iota = (uu___174_10917.iota);
                zeta = (uu___174_10917.zeta);
                weak = (uu___174_10917.weak);
                hnf = (uu___174_10917.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___174_10917.do_not_unfold_pure_lets);
                unfold_until = (uu___174_10917.unfold_until);
                unfold_only = (uu___174_10917.unfold_only);
                unfold_fully = (uu___174_10917.unfold_fully);
                unfold_attr = (uu___174_10917.unfold_attr);
                unfold_tac = (uu___174_10917.unfold_tac);
                pure_subterms_within_computations =
                  (uu___174_10917.pure_subterms_within_computations);
                simplify = (uu___174_10917.simplify);
                erase_universes = (uu___174_10917.erase_universes);
                allow_unbound_universes =
                  (uu___174_10917.allow_unbound_universes);
                reify_ = (uu___174_10917.reify_);
                compress_uvars = (uu___174_10917.compress_uvars);
                no_full_norm = (uu___174_10917.no_full_norm);
                check_no_uvars = (uu___174_10917.check_no_uvars);
                unmeta = (uu___174_10917.unmeta);
                unascribe = (uu___174_10917.unascribe);
                in_full_norm_request = (uu___174_10917.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___174_10917.weakly_reduce_scrutinee)
              });
           tcenv = (uu___173_10914.tcenv);
           debug = (uu___173_10914.debug);
           delta_level = (uu___173_10914.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___173_10914.strong);
           memoize_lazy = (uu___173_10914.memoize_lazy);
           normalize_pure_lets = (uu___173_10914.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10924 .
    FStar_Syntax_Syntax.term -> 'Auu____10924 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10939 =
        let uu____10946 =
          let uu____10947 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10947.FStar_Syntax_Syntax.n  in
        (uu____10946, args)  in
      match uu____10939 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10953::uu____10954::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10958::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10963::uu____10964::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10967 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___114_10980  ->
    match uu___114_10980 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10986 =
          let uu____10989 =
            let uu____10990 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10990  in
          [uu____10989]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10986
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10996 =
          let uu____10999 =
            let uu____11000 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11000  in
          [uu____10999]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10996
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11021 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____11021) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11067 =
          let uu____11072 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____11072 s  in
        match uu____11067 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____11088 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____11088
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____11105::(tm,uu____11107)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____11136)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____11157)::uu____11158::(tm,uu____11160)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____11201 =
            let uu____11206 = full_norm steps  in parse_steps uu____11206  in
          (match uu____11201 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____11245 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___115_11264  ->
    match uu___115_11264 with
    | (App
        (uu____11267,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11268;
                       FStar_Syntax_Syntax.vars = uu____11269;_},uu____11270,uu____11271))::uu____11272
        -> true
    | uu____11277 -> false
  
let firstn :
  'Auu____11286 .
    Prims.int ->
      'Auu____11286 Prims.list ->
        ('Auu____11286 Prims.list,'Auu____11286 Prims.list)
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
          (uu____11328,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11329;
                         FStar_Syntax_Syntax.vars = uu____11330;_},uu____11331,uu____11332))::uu____11333
          -> (cfg.steps).reify_
      | uu____11338 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11361) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11371) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11390  ->
                  match uu____11390 with
                  | (a,uu____11398) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11404 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11429 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11430 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11431 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11432 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11433 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11434 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11435 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11436 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11443 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11450 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11463 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11480 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11493 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11500 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11562  ->
                   match uu____11562 with
                   | (a,uu____11570) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11577) ->
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
                     (fun uu____11699  ->
                        match uu____11699 with
                        | (a,uu____11707) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11712,uu____11713,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11719,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11725 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11732 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11733 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12025 ->
                   let uu____12050 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12050
               | uu____12051 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12059  ->
               let uu____12060 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12061 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12062 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12069 =
                 let uu____12070 =
                   let uu____12073 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12073
                    in
                 stack_to_string uu____12070  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12060 uu____12061 uu____12062 uu____12069);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12096 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12097 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12098 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12099;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_18;
                 FStar_Syntax_Syntax.fv_qual = uu____12100;_}
               when _0_18 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12103;
                 FStar_Syntax_Syntax.fv_delta = uu____12104;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12105;
                 FStar_Syntax_Syntax.fv_delta = uu____12106;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12107);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12114 ->
               let uu____12121 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12121
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12151 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12151)
               ->
               let cfg' =
                 let uu___175_12153 = cfg  in
                 {
                   steps =
                     (let uu___176_12156 = cfg.steps  in
                      {
                        beta = (uu___176_12156.beta);
                        iota = (uu___176_12156.iota);
                        zeta = (uu___176_12156.zeta);
                        weak = (uu___176_12156.weak);
                        hnf = (uu___176_12156.hnf);
                        primops = (uu___176_12156.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___176_12156.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___176_12156.unfold_attr);
                        unfold_tac = (uu___176_12156.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___176_12156.pure_subterms_within_computations);
                        simplify = (uu___176_12156.simplify);
                        erase_universes = (uu___176_12156.erase_universes);
                        allow_unbound_universes =
                          (uu___176_12156.allow_unbound_universes);
                        reify_ = (uu___176_12156.reify_);
                        compress_uvars = (uu___176_12156.compress_uvars);
                        no_full_norm = (uu___176_12156.no_full_norm);
                        check_no_uvars = (uu___176_12156.check_no_uvars);
                        unmeta = (uu___176_12156.unmeta);
                        unascribe = (uu___176_12156.unascribe);
                        in_full_norm_request =
                          (uu___176_12156.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___176_12156.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___175_12153.tcenv);
                   debug = (uu___175_12153.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___175_12153.primitive_steps);
                   strong = (uu___175_12153.strong);
                   memoize_lazy = (uu___175_12153.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12161 = get_norm_request (norm cfg' env []) args  in
               (match uu____12161 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12190  ->
                              fun stack1  ->
                                match uu____12190 with
                                | (a,aq) ->
                                    let uu____12202 =
                                      let uu____12203 =
                                        let uu____12210 =
                                          let uu____12211 =
                                            let uu____12242 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12242, false)  in
                                          Clos uu____12211  in
                                        (uu____12210, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12203  in
                                    uu____12202 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12330  ->
                          let uu____12331 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12331);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12353 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___116_12358  ->
                                match uu___116_12358 with
                                | UnfoldUntil uu____12359 -> true
                                | UnfoldOnly uu____12360 -> true
                                | UnfoldFully uu____12363 -> true
                                | uu____12366 -> false))
                         in
                      if uu____12353
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___177_12371 = cfg  in
                      let uu____12372 =
                        let uu___178_12373 = to_fsteps s  in
                        {
                          beta = (uu___178_12373.beta);
                          iota = (uu___178_12373.iota);
                          zeta = (uu___178_12373.zeta);
                          weak = (uu___178_12373.weak);
                          hnf = (uu___178_12373.hnf);
                          primops = (uu___178_12373.primops);
                          do_not_unfold_pure_lets =
                            (uu___178_12373.do_not_unfold_pure_lets);
                          unfold_until = (uu___178_12373.unfold_until);
                          unfold_only = (uu___178_12373.unfold_only);
                          unfold_fully = (uu___178_12373.unfold_fully);
                          unfold_attr = (uu___178_12373.unfold_attr);
                          unfold_tac = (uu___178_12373.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___178_12373.pure_subterms_within_computations);
                          simplify = (uu___178_12373.simplify);
                          erase_universes = (uu___178_12373.erase_universes);
                          allow_unbound_universes =
                            (uu___178_12373.allow_unbound_universes);
                          reify_ = (uu___178_12373.reify_);
                          compress_uvars = (uu___178_12373.compress_uvars);
                          no_full_norm = (uu___178_12373.no_full_norm);
                          check_no_uvars = (uu___178_12373.check_no_uvars);
                          unmeta = (uu___178_12373.unmeta);
                          unascribe = (uu___178_12373.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___178_12373.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12372;
                        tcenv = (uu___177_12371.tcenv);
                        debug = (uu___177_12371.debug);
                        delta_level;
                        primitive_steps = (uu___177_12371.primitive_steps);
                        strong = (uu___177_12371.strong);
                        memoize_lazy = (uu___177_12371.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12382 =
                          let uu____12383 =
                            let uu____12388 = FStar_Util.now ()  in
                            (t1, uu____12388)  in
                          Debug uu____12383  in
                        uu____12382 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12392 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12392
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12401 =
                      let uu____12408 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12408, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12401  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12418 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12418  in
               let uu____12419 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12419
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12425  ->
                       let uu____12426 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12427 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12426 uu____12427);
                  if b
                  then
                    (let uu____12428 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12428 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12436 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12436) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12449),uu____12450);
                                FStar_Syntax_Syntax.sigrng = uu____12451;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12453;
                                FStar_Syntax_Syntax.sigattrs = uu____12454;_},uu____12455),uu____12456)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12515 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___117_12519  ->
                               match uu___117_12519 with
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
                          (let uu____12529 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12529))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12548) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12583,uu____12584) -> false)))
                     in
                  let uu____12601 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12617 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12617 then (true, true) else (false, false)
                     in
                  match uu____12601 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12630  ->
                            let uu____12631 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12632 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12633 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12631 uu____12632 uu____12633);
                       if should_delta2
                       then
                         (let uu____12634 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___179_12644 = cfg  in
                                 {
                                   steps =
                                     (let uu___180_12647 = cfg.steps  in
                                      {
                                        beta = (uu___180_12647.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___180_12647.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___180_12647.unfold_attr);
                                        unfold_tac =
                                          (uu___180_12647.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___180_12647.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___180_12647.erase_universes);
                                        allow_unbound_universes =
                                          (uu___180_12647.allow_unbound_universes);
                                        reify_ = (uu___180_12647.reify_);
                                        compress_uvars =
                                          (uu___180_12647.compress_uvars);
                                        no_full_norm =
                                          (uu___180_12647.no_full_norm);
                                        check_no_uvars =
                                          (uu___180_12647.check_no_uvars);
                                        unmeta = (uu___180_12647.unmeta);
                                        unascribe =
                                          (uu___180_12647.unascribe);
                                        in_full_norm_request =
                                          (uu___180_12647.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___180_12647.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___179_12644.tcenv);
                                   debug = (uu___179_12644.debug);
                                   delta_level = (uu___179_12644.delta_level);
                                   primitive_steps =
                                     (uu___179_12644.primitive_steps);
                                   strong = (uu___179_12644.strong);
                                   memoize_lazy =
                                     (uu___179_12644.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___179_12644.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12634 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12657 = lookup_bvar env x  in
               (match uu____12657 with
                | Univ uu____12658 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12707 = FStar_ST.op_Bang r  in
                      (match uu____12707 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12829  ->
                                 let uu____12830 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12831 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12830
                                   uu____12831);
                            (let uu____12832 = maybe_weakly_reduced t'  in
                             if uu____12832
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12833 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12904)::uu____12905 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12914)::uu____12915 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12927,uu____12928))::stack_rest ->
                    (match c with
                     | Univ uu____12932 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12941 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12962  ->
                                    let uu____12963 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12963);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12991  ->
                                    let uu____12992 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12992);
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
                       (fun uu____13058  ->
                          let uu____13059 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13059);
                     norm cfg env stack1 t1)
                | (Debug uu____13060)::uu____13061 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___181_13071 = cfg.steps  in
                             {
                               beta = (uu___181_13071.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___181_13071.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___181_13071.unfold_until);
                               unfold_only = (uu___181_13071.unfold_only);
                               unfold_fully = (uu___181_13071.unfold_fully);
                               unfold_attr = (uu___181_13071.unfold_attr);
                               unfold_tac = (uu___181_13071.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___181_13071.erase_universes);
                               allow_unbound_universes =
                                 (uu___181_13071.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___181_13071.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___181_13071.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___181_13071.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___181_13071.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___182_13073 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___182_13073.tcenv);
                               debug = (uu___182_13073.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___182_13073.primitive_steps);
                               strong = (uu___182_13073.strong);
                               memoize_lazy = (uu___182_13073.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___182_13073.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13075 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13075 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13107  -> dummy :: env1) env)
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
                                          let uu____13148 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13148)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___183_13153 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___183_13153.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___183_13153.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13154 -> lopt  in
                           (log cfg
                              (fun uu____13160  ->
                                 let uu____13161 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13161);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___184_13170 = cfg  in
                               {
                                 steps = (uu___184_13170.steps);
                                 tcenv = (uu___184_13170.tcenv);
                                 debug = (uu___184_13170.debug);
                                 delta_level = (uu___184_13170.delta_level);
                                 primitive_steps =
                                   (uu___184_13170.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___184_13170.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_13170.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13173)::uu____13174 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___181_13186 = cfg.steps  in
                             {
                               beta = (uu___181_13186.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___181_13186.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___181_13186.unfold_until);
                               unfold_only = (uu___181_13186.unfold_only);
                               unfold_fully = (uu___181_13186.unfold_fully);
                               unfold_attr = (uu___181_13186.unfold_attr);
                               unfold_tac = (uu___181_13186.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___181_13186.erase_universes);
                               allow_unbound_universes =
                                 (uu___181_13186.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___181_13186.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___181_13186.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___181_13186.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___181_13186.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___182_13188 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___182_13188.tcenv);
                               debug = (uu___182_13188.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___182_13188.primitive_steps);
                               strong = (uu___182_13188.strong);
                               memoize_lazy = (uu___182_13188.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___182_13188.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13190 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13190 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13222  -> dummy :: env1) env)
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
                                          let uu____13263 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13263)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___183_13268 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___183_13268.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___183_13268.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13269 -> lopt  in
                           (log cfg
                              (fun uu____13275  ->
                                 let uu____13276 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13276);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___184_13285 = cfg  in
                               {
                                 steps = (uu___184_13285.steps);
                                 tcenv = (uu___184_13285.tcenv);
                                 debug = (uu___184_13285.debug);
                                 delta_level = (uu___184_13285.delta_level);
                                 primitive_steps =
                                   (uu___184_13285.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___184_13285.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_13285.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13288)::uu____13289 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___181_13303 = cfg.steps  in
                             {
                               beta = (uu___181_13303.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___181_13303.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___181_13303.unfold_until);
                               unfold_only = (uu___181_13303.unfold_only);
                               unfold_fully = (uu___181_13303.unfold_fully);
                               unfold_attr = (uu___181_13303.unfold_attr);
                               unfold_tac = (uu___181_13303.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___181_13303.erase_universes);
                               allow_unbound_universes =
                                 (uu___181_13303.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___181_13303.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___181_13303.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___181_13303.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___181_13303.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___182_13305 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___182_13305.tcenv);
                               debug = (uu___182_13305.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___182_13305.primitive_steps);
                               strong = (uu___182_13305.strong);
                               memoize_lazy = (uu___182_13305.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___182_13305.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13307 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13307 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13339  -> dummy :: env1) env)
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
                                          let uu____13380 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13380)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___183_13385 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___183_13385.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___183_13385.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13386 -> lopt  in
                           (log cfg
                              (fun uu____13392  ->
                                 let uu____13393 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13393);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___184_13402 = cfg  in
                               {
                                 steps = (uu___184_13402.steps);
                                 tcenv = (uu___184_13402.tcenv);
                                 debug = (uu___184_13402.debug);
                                 delta_level = (uu___184_13402.delta_level);
                                 primitive_steps =
                                   (uu___184_13402.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___184_13402.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_13402.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13405)::uu____13406 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___181_13420 = cfg.steps  in
                             {
                               beta = (uu___181_13420.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___181_13420.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___181_13420.unfold_until);
                               unfold_only = (uu___181_13420.unfold_only);
                               unfold_fully = (uu___181_13420.unfold_fully);
                               unfold_attr = (uu___181_13420.unfold_attr);
                               unfold_tac = (uu___181_13420.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___181_13420.erase_universes);
                               allow_unbound_universes =
                                 (uu___181_13420.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___181_13420.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___181_13420.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___181_13420.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___181_13420.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___182_13422 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___182_13422.tcenv);
                               debug = (uu___182_13422.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___182_13422.primitive_steps);
                               strong = (uu___182_13422.strong);
                               memoize_lazy = (uu___182_13422.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___182_13422.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13424 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13424 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13456  -> dummy :: env1) env)
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
                                          let uu____13497 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13497)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___183_13502 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___183_13502.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___183_13502.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13503 -> lopt  in
                           (log cfg
                              (fun uu____13509  ->
                                 let uu____13510 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13510);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___184_13519 = cfg  in
                               {
                                 steps = (uu___184_13519.steps);
                                 tcenv = (uu___184_13519.tcenv);
                                 debug = (uu___184_13519.debug);
                                 delta_level = (uu___184_13519.delta_level);
                                 primitive_steps =
                                   (uu___184_13519.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___184_13519.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_13519.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13522)::uu____13523 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___181_13541 = cfg.steps  in
                             {
                               beta = (uu___181_13541.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___181_13541.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___181_13541.unfold_until);
                               unfold_only = (uu___181_13541.unfold_only);
                               unfold_fully = (uu___181_13541.unfold_fully);
                               unfold_attr = (uu___181_13541.unfold_attr);
                               unfold_tac = (uu___181_13541.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___181_13541.erase_universes);
                               allow_unbound_universes =
                                 (uu___181_13541.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___181_13541.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___181_13541.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___181_13541.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___181_13541.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___182_13543 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___182_13543.tcenv);
                               debug = (uu___182_13543.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___182_13543.primitive_steps);
                               strong = (uu___182_13543.strong);
                               memoize_lazy = (uu___182_13543.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___182_13543.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13545 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13545 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13577  -> dummy :: env1) env)
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
                                          let uu____13618 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13618)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___183_13623 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___183_13623.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___183_13623.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13624 -> lopt  in
                           (log cfg
                              (fun uu____13630  ->
                                 let uu____13631 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13631);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___184_13640 = cfg  in
                               {
                                 steps = (uu___184_13640.steps);
                                 tcenv = (uu___184_13640.tcenv);
                                 debug = (uu___184_13640.debug);
                                 delta_level = (uu___184_13640.delta_level);
                                 primitive_steps =
                                   (uu___184_13640.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___184_13640.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_13640.normalize_pure_lets)
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
                             let uu___181_13646 = cfg.steps  in
                             {
                               beta = (uu___181_13646.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___181_13646.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___181_13646.unfold_until);
                               unfold_only = (uu___181_13646.unfold_only);
                               unfold_fully = (uu___181_13646.unfold_fully);
                               unfold_attr = (uu___181_13646.unfold_attr);
                               unfold_tac = (uu___181_13646.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___181_13646.erase_universes);
                               allow_unbound_universes =
                                 (uu___181_13646.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___181_13646.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___181_13646.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___181_13646.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___181_13646.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___182_13648 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___182_13648.tcenv);
                               debug = (uu___182_13648.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___182_13648.primitive_steps);
                               strong = (uu___182_13648.strong);
                               memoize_lazy = (uu___182_13648.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___182_13648.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13650 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13650 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13682  -> dummy :: env1) env)
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
                                          let uu____13723 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13723)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___183_13728 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___183_13728.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___183_13728.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13729 -> lopt  in
                           (log cfg
                              (fun uu____13735  ->
                                 let uu____13736 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13736);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___184_13745 = cfg  in
                               {
                                 steps = (uu___184_13745.steps);
                                 tcenv = (uu___184_13745.tcenv);
                                 debug = (uu___184_13745.debug);
                                 delta_level = (uu___184_13745.delta_level);
                                 primitive_steps =
                                   (uu___184_13745.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___184_13745.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___184_13745.normalize_pure_lets)
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
                      (fun uu____13784  ->
                         fun stack1  ->
                           match uu____13784 with
                           | (a,aq) ->
                               let uu____13796 =
                                 let uu____13797 =
                                   let uu____13804 =
                                     let uu____13805 =
                                       let uu____13836 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13836, false)  in
                                     Clos uu____13805  in
                                   (uu____13804, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13797  in
                               uu____13796 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13924  ->
                     let uu____13925 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13925);
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
                             ((let uu___185_13971 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___185_13971.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___185_13971.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13972 ->
                      let uu____13987 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13987)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13990 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13990 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14015 =
                          let uu____14016 =
                            let uu____14023 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___186_14029 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___186_14029.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___186_14029.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14023)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14016  in
                        mk uu____14015 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14048 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14048
               else
                 (let uu____14050 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14050 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14058 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14080  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14058 c1  in
                      let t2 =
                        let uu____14102 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14102 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14213)::uu____14214 ->
                    (log cfg
                       (fun uu____14227  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14228)::uu____14229 ->
                    (log cfg
                       (fun uu____14240  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14241,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14242;
                                   FStar_Syntax_Syntax.vars = uu____14243;_},uu____14244,uu____14245))::uu____14246
                    ->
                    (log cfg
                       (fun uu____14253  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14254)::uu____14255 ->
                    (log cfg
                       (fun uu____14266  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14267 ->
                    (log cfg
                       (fun uu____14270  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14274  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14299 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14299
                         | FStar_Util.Inr c ->
                             let uu____14309 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14309
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14328 =
                               let uu____14329 =
                                 let uu____14356 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14356, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14329
                                in
                             mk uu____14328 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14391 ->
                           let uu____14392 =
                             let uu____14393 =
                               let uu____14394 =
                                 let uu____14421 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14421, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14394
                                in
                             mk uu____14393 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14392))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___187_14498 = cfg  in
                   {
                     steps =
                       (let uu___188_14501 = cfg.steps  in
                        {
                          beta = (uu___188_14501.beta);
                          iota = (uu___188_14501.iota);
                          zeta = (uu___188_14501.zeta);
                          weak = true;
                          hnf = (uu___188_14501.hnf);
                          primops = (uu___188_14501.primops);
                          do_not_unfold_pure_lets =
                            (uu___188_14501.do_not_unfold_pure_lets);
                          unfold_until = (uu___188_14501.unfold_until);
                          unfold_only = (uu___188_14501.unfold_only);
                          unfold_fully = (uu___188_14501.unfold_fully);
                          unfold_attr = (uu___188_14501.unfold_attr);
                          unfold_tac = (uu___188_14501.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___188_14501.pure_subterms_within_computations);
                          simplify = (uu___188_14501.simplify);
                          erase_universes = (uu___188_14501.erase_universes);
                          allow_unbound_universes =
                            (uu___188_14501.allow_unbound_universes);
                          reify_ = (uu___188_14501.reify_);
                          compress_uvars = (uu___188_14501.compress_uvars);
                          no_full_norm = (uu___188_14501.no_full_norm);
                          check_no_uvars = (uu___188_14501.check_no_uvars);
                          unmeta = (uu___188_14501.unmeta);
                          unascribe = (uu___188_14501.unascribe);
                          in_full_norm_request =
                            (uu___188_14501.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___188_14501.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___187_14498.tcenv);
                     debug = (uu___187_14498.debug);
                     delta_level = (uu___187_14498.delta_level);
                     primitive_steps = (uu___187_14498.primitive_steps);
                     strong = (uu___187_14498.strong);
                     memoize_lazy = (uu___187_14498.memoize_lazy);
                     normalize_pure_lets =
                       (uu___187_14498.normalize_pure_lets)
                   }
                 else cfg  in
               norm cfg1 env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____14537 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14537 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___189_14557 = cfg  in
                               let uu____14558 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___189_14557.steps);
                                 tcenv = uu____14558;
                                 debug = (uu___189_14557.debug);
                                 delta_level = (uu___189_14557.delta_level);
                                 primitive_steps =
                                   (uu___189_14557.primitive_steps);
                                 strong = (uu___189_14557.strong);
                                 memoize_lazy = (uu___189_14557.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___189_14557.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14565 =
                                 let uu____14566 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14566  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14565
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___190_14569 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___190_14569.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___190_14569.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___190_14569.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___190_14569.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14570 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14570
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14581,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14582;
                               FStar_Syntax_Syntax.lbunivs = uu____14583;
                               FStar_Syntax_Syntax.lbtyp = uu____14584;
                               FStar_Syntax_Syntax.lbeff = uu____14585;
                               FStar_Syntax_Syntax.lbdef = uu____14586;
                               FStar_Syntax_Syntax.lbattrs = uu____14587;
                               FStar_Syntax_Syntax.lbpos = uu____14588;_}::uu____14589),uu____14590)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14630 =
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
               if uu____14630
               then
                 let binder =
                   let uu____14632 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14632  in
                 let env1 =
                   let uu____14642 =
                     let uu____14649 =
                       let uu____14650 =
                         let uu____14681 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14681,
                           false)
                          in
                       Clos uu____14650  in
                     ((FStar_Pervasives_Native.Some binder), uu____14649)  in
                   uu____14642 :: env  in
                 (log cfg
                    (fun uu____14776  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14780  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14781 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14781))
                 else
                   (let uu____14783 =
                      let uu____14788 =
                        let uu____14789 =
                          let uu____14794 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14794
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14789]  in
                      FStar_Syntax_Subst.open_term uu____14788 body  in
                    match uu____14783 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14815  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14823 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14823  in
                            FStar_Util.Inl
                              (let uu___191_14833 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___191_14833.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___191_14833.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14836  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___192_14838 = lb  in
                             let uu____14839 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___192_14838.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___192_14838.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14839;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___192_14838.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___192_14838.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14864  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___193_14887 = cfg  in
                             {
                               steps = (uu___193_14887.steps);
                               tcenv = (uu___193_14887.tcenv);
                               debug = (uu___193_14887.debug);
                               delta_level = (uu___193_14887.delta_level);
                               primitive_steps =
                                 (uu___193_14887.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___193_14887.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___193_14887.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14890  ->
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
               let uu____14907 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14907 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14943 =
                               let uu___194_14944 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___194_14944.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___194_14944.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14943  in
                           let uu____14945 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14945 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14971 =
                                   FStar_List.map (fun uu____14987  -> dummy)
                                     lbs1
                                    in
                                 let uu____14988 =
                                   let uu____14997 =
                                     FStar_List.map
                                       (fun uu____15017  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14997 env  in
                                 FStar_List.append uu____14971 uu____14988
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15041 =
                                       let uu___195_15042 = rc  in
                                       let uu____15043 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___195_15042.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15043;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___195_15042.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15041
                                 | uu____15052 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___196_15058 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___196_15058.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___196_15058.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___196_15058.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___196_15058.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15068 =
                        FStar_List.map (fun uu____15084  -> dummy) lbs2  in
                      FStar_List.append uu____15068 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15092 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15092 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___197_15108 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___197_15108.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___197_15108.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15137 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15137
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15156 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15232  ->
                        match uu____15232 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___198_15353 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___198_15353.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___198_15353.FStar_Syntax_Syntax.sort)
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
               (match uu____15156 with
                | (rec_env,memos,uu____15580) ->
                    let uu____15633 =
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
                             let uu____15956 =
                               let uu____15963 =
                                 let uu____15964 =
                                   let uu____15995 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15995, false)
                                    in
                                 Clos uu____15964  in
                               (FStar_Pervasives_Native.None, uu____15963)
                                in
                             uu____15956 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16099  ->
                     let uu____16100 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16100);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16122 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16124::uu____16125 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16130) ->
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
                             | uu____16153 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16167 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16167
                              | uu____16178 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16184 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16210 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16212 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16213 =
                        let uu____16214 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16215 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16214 uu____16215
                         in
                      failwith uu____16213
                    else rebuild cfg env stack t2
                | uu____16217 -> norm cfg env stack t2))

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
                let uu____16227 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16227  in
              let uu____16228 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16228 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16241  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16252  ->
                        let uu____16253 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16254 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16253 uu____16254);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16259 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16259 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16268))::stack1 ->
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
                      | uu____16307 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16310 ->
                          let uu____16313 =
                            let uu____16314 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16314
                             in
                          failwith uu____16313
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
                  let uu___199_16338 = cfg  in
                  let uu____16339 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16339;
                    tcenv = (uu___199_16338.tcenv);
                    debug = (uu___199_16338.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___199_16338.primitive_steps);
                    strong = (uu___199_16338.strong);
                    memoize_lazy = (uu___199_16338.memoize_lazy);
                    normalize_pure_lets =
                      (uu___199_16338.normalize_pure_lets)
                  }
                else
                  (let uu___200_16341 = cfg  in
                   {
                     steps =
                       (let uu___201_16344 = cfg.steps  in
                        {
                          beta = (uu___201_16344.beta);
                          iota = (uu___201_16344.iota);
                          zeta = false;
                          weak = (uu___201_16344.weak);
                          hnf = (uu___201_16344.hnf);
                          primops = (uu___201_16344.primops);
                          do_not_unfold_pure_lets =
                            (uu___201_16344.do_not_unfold_pure_lets);
                          unfold_until = (uu___201_16344.unfold_until);
                          unfold_only = (uu___201_16344.unfold_only);
                          unfold_fully = (uu___201_16344.unfold_fully);
                          unfold_attr = (uu___201_16344.unfold_attr);
                          unfold_tac = (uu___201_16344.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___201_16344.pure_subterms_within_computations);
                          simplify = (uu___201_16344.simplify);
                          erase_universes = (uu___201_16344.erase_universes);
                          allow_unbound_universes =
                            (uu___201_16344.allow_unbound_universes);
                          reify_ = (uu___201_16344.reify_);
                          compress_uvars = (uu___201_16344.compress_uvars);
                          no_full_norm = (uu___201_16344.no_full_norm);
                          check_no_uvars = (uu___201_16344.check_no_uvars);
                          unmeta = (uu___201_16344.unmeta);
                          unascribe = (uu___201_16344.unascribe);
                          in_full_norm_request =
                            (uu___201_16344.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___201_16344.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___200_16341.tcenv);
                     debug = (uu___200_16341.debug);
                     delta_level = (uu___200_16341.delta_level);
                     primitive_steps = (uu___200_16341.primitive_steps);
                     strong = (uu___200_16341.strong);
                     memoize_lazy = (uu___200_16341.memoize_lazy);
                     normalize_pure_lets =
                       (uu___200_16341.normalize_pure_lets)
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
                  (fun uu____16378  ->
                     let uu____16379 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16380 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16379
                       uu____16380);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16382 =
                   let uu____16383 = FStar_Syntax_Subst.compress head3  in
                   uu____16383.FStar_Syntax_Syntax.n  in
                 match uu____16382 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16401 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16401
                        in
                     let uu____16402 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16402 with
                      | (uu____16403,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16413 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16423 =
                                   let uu____16424 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16424.FStar_Syntax_Syntax.n  in
                                 match uu____16423 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16430,uu____16431))
                                     ->
                                     let uu____16440 =
                                       let uu____16441 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16441.FStar_Syntax_Syntax.n  in
                                     (match uu____16440 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16447,msrc,uu____16449))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16458 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16458
                                      | uu____16459 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16460 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16461 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16461 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___202_16466 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___202_16466.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___202_16466.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___202_16466.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___202_16466.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___202_16466.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16467 = FStar_List.tl stack  in
                                    let uu____16468 =
                                      let uu____16469 =
                                        let uu____16476 =
                                          let uu____16477 =
                                            let uu____16490 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16490)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16477
                                           in
                                        FStar_Syntax_Syntax.mk uu____16476
                                         in
                                      uu____16469
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16467 uu____16468
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16506 =
                                      let uu____16507 = is_return body  in
                                      match uu____16507 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16511;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16512;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16515 -> false  in
                                    if uu____16506
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
                                         let uu____16536 =
                                           let uu____16543 =
                                             let uu____16544 =
                                               let uu____16561 =
                                                 let uu____16568 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16568]  in
                                               (uu____16561, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16544
                                              in
                                           FStar_Syntax_Syntax.mk uu____16543
                                            in
                                         uu____16536
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16602 =
                                           let uu____16603 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16603.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16602 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16609::uu____16610::[])
                                             ->
                                             let uu____16615 =
                                               let uu____16622 =
                                                 let uu____16623 =
                                                   let uu____16630 =
                                                     let uu____16631 =
                                                       let uu____16632 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16632
                                                        in
                                                     let uu____16633 =
                                                       let uu____16636 =
                                                         let uu____16637 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16637
                                                          in
                                                       [uu____16636]  in
                                                     uu____16631 ::
                                                       uu____16633
                                                      in
                                                   (bind1, uu____16630)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16623
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16622
                                                in
                                             uu____16615
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16643 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16655 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16655
                                         then
                                           let uu____16664 =
                                             let uu____16671 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16671
                                              in
                                           let uu____16672 =
                                             let uu____16681 =
                                               let uu____16688 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16688
                                                in
                                             [uu____16681]  in
                                           uu____16664 :: uu____16672
                                         else []  in
                                       let reified =
                                         let uu____16717 =
                                           let uu____16724 =
                                             let uu____16725 =
                                               let uu____16740 =
                                                 let uu____16749 =
                                                   let uu____16758 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16765 =
                                                     let uu____16774 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16774]  in
                                                   uu____16758 :: uu____16765
                                                    in
                                                 let uu____16799 =
                                                   let uu____16808 =
                                                     let uu____16817 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16824 =
                                                       let uu____16833 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16840 =
                                                         let uu____16849 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16856 =
                                                           let uu____16865 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16865]  in
                                                         uu____16849 ::
                                                           uu____16856
                                                          in
                                                       uu____16833 ::
                                                         uu____16840
                                                        in
                                                     uu____16817 ::
                                                       uu____16824
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16808
                                                    in
                                                 FStar_List.append
                                                   uu____16749 uu____16799
                                                  in
                                               (bind_inst, uu____16740)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16725
                                              in
                                           FStar_Syntax_Syntax.mk uu____16724
                                            in
                                         uu____16717
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16931  ->
                                            let uu____16932 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16933 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16932 uu____16933);
                                       (let uu____16934 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16934 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16958 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16958
                        in
                     let uu____16959 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16959 with
                      | (uu____16960,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16997 =
                                  let uu____16998 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16998.FStar_Syntax_Syntax.n  in
                                match uu____16997 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17002) -> t2
                                | uu____17007 -> head4  in
                              let uu____17008 =
                                let uu____17009 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17009.FStar_Syntax_Syntax.n  in
                              match uu____17008 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17015 -> FStar_Pervasives_Native.None
                               in
                            let uu____17016 = maybe_extract_fv head4  in
                            match uu____17016 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17026 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17026
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17031 = maybe_extract_fv head5
                                     in
                                  match uu____17031 with
                                  | FStar_Pervasives_Native.Some uu____17036
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17037 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17042 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17057 =
                              match uu____17057 with
                              | (e,q) ->
                                  let uu____17064 =
                                    let uu____17065 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17065.FStar_Syntax_Syntax.n  in
                                  (match uu____17064 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17080 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17080
                                   | uu____17081 -> false)
                               in
                            let uu____17082 =
                              let uu____17083 =
                                let uu____17092 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17092 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17083
                               in
                            if uu____17082
                            then
                              let uu____17111 =
                                let uu____17112 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17112
                                 in
                              failwith uu____17111
                            else ());
                           (let uu____17114 = maybe_unfold_action head_app
                               in
                            match uu____17114 with
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
                                   (fun uu____17157  ->
                                      let uu____17158 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17159 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17158 uu____17159);
                                 (let uu____17160 = FStar_List.tl stack  in
                                  norm cfg env uu____17160 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17162) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17186 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17186  in
                     (log cfg
                        (fun uu____17190  ->
                           let uu____17191 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17191);
                      (let uu____17192 = FStar_List.tl stack  in
                       norm cfg env uu____17192 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17313  ->
                               match uu____17313 with
                               | (pat,wopt,tm) ->
                                   let uu____17361 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17361)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17393 = FStar_List.tl stack  in
                     norm cfg env uu____17393 tm
                 | uu____17394 -> fallback ())

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
              (fun uu____17408  ->
                 let uu____17409 = FStar_Ident.string_of_lid msrc  in
                 let uu____17410 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17411 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17409
                   uu____17410 uu____17411);
            (let uu____17412 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17412
             then
               let ed =
                 let uu____17414 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17414  in
               let uu____17415 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17415 with
               | (uu____17416,return_repr) ->
                   let return_inst =
                     let uu____17429 =
                       let uu____17430 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17430.FStar_Syntax_Syntax.n  in
                     match uu____17429 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17436::[]) ->
                         let uu____17441 =
                           let uu____17448 =
                             let uu____17449 =
                               let uu____17456 =
                                 let uu____17457 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17457]  in
                               (return_tm, uu____17456)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17449  in
                           FStar_Syntax_Syntax.mk uu____17448  in
                         uu____17441 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17463 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17466 =
                     let uu____17473 =
                       let uu____17474 =
                         let uu____17489 =
                           let uu____17498 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17505 =
                             let uu____17514 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17514]  in
                           uu____17498 :: uu____17505  in
                         (return_inst, uu____17489)  in
                       FStar_Syntax_Syntax.Tm_app uu____17474  in
                     FStar_Syntax_Syntax.mk uu____17473  in
                   uu____17466 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17553 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17553 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17556 =
                      let uu____17557 = FStar_Ident.text_of_lid msrc  in
                      let uu____17558 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17557 uu____17558
                       in
                    failwith uu____17556
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17559;
                      FStar_TypeChecker_Env.mtarget = uu____17560;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17561;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17583 =
                      let uu____17584 = FStar_Ident.text_of_lid msrc  in
                      let uu____17585 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17584 uu____17585
                       in
                    failwith uu____17583
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17586;
                      FStar_TypeChecker_Env.mtarget = uu____17587;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17588;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17623 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17624 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17623 t FStar_Syntax_Syntax.tun uu____17624))

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
                (fun uu____17680  ->
                   match uu____17680 with
                   | (a,imp) ->
                       let uu____17691 = norm cfg env [] a  in
                       (uu____17691, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17699  ->
             let uu____17700 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17701 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17700 uu____17701);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17725 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17725
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___203_17728 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___203_17728.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___203_17728.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17750 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____17750
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___204_17753 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___204_17753.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___204_17753.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17790  ->
                      match uu____17790 with
                      | (a,i) ->
                          let uu____17801 = norm cfg env [] a  in
                          (uu____17801, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___118_17819  ->
                       match uu___118_17819 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17823 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17823
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___205_17831 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___206_17834 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___206_17834.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___205_17831.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___205_17831.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17837  ->
        match uu____17837 with
        | (x,imp) ->
            let uu____17840 =
              let uu___207_17841 = x  in
              let uu____17842 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___207_17841.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___207_17841.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17842
              }  in
            (uu____17840, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17848 =
          FStar_List.fold_left
            (fun uu____17882  ->
               fun b  ->
                 match uu____17882 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17848 with | (nbs,uu____17962) -> FStar_List.rev nbs

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
            let uu____17994 =
              let uu___208_17995 = rc  in
              let uu____17996 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___208_17995.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17996;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___208_17995.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17994
        | uu____18005 -> lopt

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
            (let uu____18026 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18027 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____18026
               uu____18027)
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
          let uu____18049 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18049
          then tm1
          else
            (let w t =
               let uu___209_18063 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___209_18063.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___209_18063.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18074 =
                 let uu____18075 = FStar_Syntax_Util.unmeta t  in
                 uu____18075.FStar_Syntax_Syntax.n  in
               match uu____18074 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18082 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18131)::args1,(bv,uu____18134)::bs1) ->
                   let uu____18168 =
                     let uu____18169 = FStar_Syntax_Subst.compress t  in
                     uu____18169.FStar_Syntax_Syntax.n  in
                   (match uu____18168 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18173 -> false)
               | ([],[]) -> true
               | (uu____18194,uu____18195) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18236 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18237 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18236
                    uu____18237)
               else ();
               (let uu____18239 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18239 with
                | (hd1,args) ->
                    let uu____18272 =
                      let uu____18273 = FStar_Syntax_Subst.compress hd1  in
                      uu____18273.FStar_Syntax_Syntax.n  in
                    (match uu____18272 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____18280 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18281 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18282 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18280 uu____18281 uu____18282)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18284 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18301 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18302 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18301
                    uu____18302)
               else ();
               (let uu____18304 = FStar_Syntax_Util.is_squash t  in
                match uu____18304 with
                | FStar_Pervasives_Native.Some (uu____18315,t') ->
                    is_applied bs t'
                | uu____18327 ->
                    let uu____18336 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18336 with
                     | FStar_Pervasives_Native.Some (uu____18347,t') ->
                         is_applied bs t'
                     | uu____18359 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18383 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18383 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18390)::(q,uu____18392)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18420 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18421 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18420 uu____18421)
                    else ();
                    (let uu____18423 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18423 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18428 =
                           let uu____18429 = FStar_Syntax_Subst.compress p
                              in
                           uu____18429.FStar_Syntax_Syntax.n  in
                         (match uu____18428 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18437 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18437))
                          | uu____18440 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18443)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18460 =
                           let uu____18461 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18461.FStar_Syntax_Syntax.n  in
                         (match uu____18460 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18469 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18469))
                          | uu____18472 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18476 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18476 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18481 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18481 with
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
                                     let uu____18492 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18492))
                               | uu____18495 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18500)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18517 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18517 with
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
                                     let uu____18528 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18528))
                               | uu____18531 -> FStar_Pervasives_Native.None)
                          | uu____18534 -> FStar_Pervasives_Native.None)
                     | uu____18537 -> FStar_Pervasives_Native.None))
               | uu____18540 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18553 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18553 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18559)::[],uu____18560,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18571 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18572 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18571
                         uu____18572)
                    else ();
                    is_quantified_const bv phi')
               | uu____18574 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18587 =
                 let uu____18588 = FStar_Syntax_Subst.compress phi  in
                 uu____18588.FStar_Syntax_Syntax.n  in
               match uu____18587 with
               | FStar_Syntax_Syntax.Tm_match (uu____18593,br::brs) ->
                   let uu____18660 = br  in
                   (match uu____18660 with
                    | (uu____18677,uu____18678,e) ->
                        let r =
                          let uu____18699 = simp_t e  in
                          match uu____18699 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18705 =
                                FStar_List.for_all
                                  (fun uu____18723  ->
                                     match uu____18723 with
                                     | (uu____18736,uu____18737,e') ->
                                         let uu____18751 = simp_t e'  in
                                         uu____18751 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18705
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18759 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18768 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18768
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18799 =
                 match uu____18799 with
                 | (t1,q) ->
                     let uu____18812 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18812 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18840 -> (t1, q))
                  in
               let uu____18851 = FStar_Syntax_Util.head_and_args t  in
               match uu____18851 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18917 =
                 let uu____18918 = FStar_Syntax_Util.unmeta ty  in
                 uu____18918.FStar_Syntax_Syntax.n  in
               match uu____18917 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18922) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18927,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18947 -> false  in
             let simplify1 arg =
               let uu____18972 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18972, arg)  in
             let uu____18981 = is_forall_const tm1  in
             match uu____18981 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____18986 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18987 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18986
                       uu____18987)
                  else ();
                  (let uu____18989 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18989))
             | FStar_Pervasives_Native.None  ->
                 let uu____18990 =
                   let uu____18991 = FStar_Syntax_Subst.compress tm1  in
                   uu____18991.FStar_Syntax_Syntax.n  in
                 (match uu____18990 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18995;
                              FStar_Syntax_Syntax.vars = uu____18996;_},uu____18997);
                         FStar_Syntax_Syntax.pos = uu____18998;
                         FStar_Syntax_Syntax.vars = uu____18999;_},args)
                      ->
                      let uu____19025 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19025
                      then
                        let uu____19026 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19026 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19071)::
                             (uu____19072,(arg,uu____19074))::[] ->
                             maybe_auto_squash arg
                         | (uu____19123,(arg,uu____19125))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19126)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19175)::uu____19176::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19227::(FStar_Pervasives_Native.Some (false
                                         ),uu____19228)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19279 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19293 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19293
                         then
                           let uu____19294 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19294 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19339)::uu____19340::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19391::(FStar_Pervasives_Native.Some (true
                                           ),uu____19392)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19443)::(uu____19444,(arg,uu____19446))::[]
                               -> maybe_auto_squash arg
                           | (uu____19495,(arg,uu____19497))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19498)::[]
                               -> maybe_auto_squash arg
                           | uu____19547 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19561 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19561
                            then
                              let uu____19562 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19562 with
                              | uu____19607::(FStar_Pervasives_Native.Some
                                              (true ),uu____19608)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19659)::uu____19660::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19711)::(uu____19712,(arg,uu____19714))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19763,(p,uu____19765))::(uu____19766,
                                                                (q,uu____19768))::[]
                                  ->
                                  let uu____19815 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19815
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19817 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19831 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19831
                               then
                                 let uu____19832 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19832 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19877)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19878)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19929)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19930)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19981)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19982)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20033)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20034)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20085,(arg,uu____20087))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20088)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20137)::(uu____20138,(arg,uu____20140))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20189,(arg,uu____20191))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20192)::[]
                                     ->
                                     let uu____20241 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20241
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20242)::(uu____20243,(arg,uu____20245))::[]
                                     ->
                                     let uu____20294 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20294
                                 | (uu____20295,(p,uu____20297))::(uu____20298,
                                                                   (q,uu____20300))::[]
                                     ->
                                     let uu____20347 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20347
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20349 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20363 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20363
                                  then
                                    let uu____20364 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20364 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20409)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20440)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20471 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20485 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20485
                                     then
                                       match args with
                                       | (t,uu____20487)::[] ->
                                           let uu____20504 =
                                             let uu____20505 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20505.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20504 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20508::[],body,uu____20510)
                                                ->
                                                let uu____20537 = simp_t body
                                                   in
                                                (match uu____20537 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20540 -> tm1)
                                            | uu____20543 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20545))::(t,uu____20547)::[]
                                           ->
                                           let uu____20574 =
                                             let uu____20575 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20575.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20574 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20578::[],body,uu____20580)
                                                ->
                                                let uu____20607 = simp_t body
                                                   in
                                                (match uu____20607 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20610 -> tm1)
                                            | uu____20613 -> tm1)
                                       | uu____20614 -> tm1
                                     else
                                       (let uu____20624 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20624
                                        then
                                          match args with
                                          | (t,uu____20626)::[] ->
                                              let uu____20643 =
                                                let uu____20644 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20644.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20643 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20647::[],body,uu____20649)
                                                   ->
                                                   let uu____20676 =
                                                     simp_t body  in
                                                   (match uu____20676 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20679 -> tm1)
                                               | uu____20682 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20684))::(t,uu____20686)::[]
                                              ->
                                              let uu____20713 =
                                                let uu____20714 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20714.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20713 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20717::[],body,uu____20719)
                                                   ->
                                                   let uu____20746 =
                                                     simp_t body  in
                                                   (match uu____20746 with
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
                                                    | uu____20749 -> tm1)
                                               | uu____20752 -> tm1)
                                          | uu____20753 -> tm1
                                        else
                                          (let uu____20763 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20763
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20764;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20765;_},uu____20766)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20783;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20784;_},uu____20785)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20802 -> tm1
                                           else
                                             (let uu____20812 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20812 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20832 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20842;
                         FStar_Syntax_Syntax.vars = uu____20843;_},args)
                      ->
                      let uu____20865 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20865
                      then
                        let uu____20866 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20866 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20911)::
                             (uu____20912,(arg,uu____20914))::[] ->
                             maybe_auto_squash arg
                         | (uu____20963,(arg,uu____20965))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20966)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21015)::uu____21016::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21067::(FStar_Pervasives_Native.Some (false
                                         ),uu____21068)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21119 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21133 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21133
                         then
                           let uu____21134 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21134 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21179)::uu____21180::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21231::(FStar_Pervasives_Native.Some (true
                                           ),uu____21232)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21283)::(uu____21284,(arg,uu____21286))::[]
                               -> maybe_auto_squash arg
                           | (uu____21335,(arg,uu____21337))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21338)::[]
                               -> maybe_auto_squash arg
                           | uu____21387 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21401 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21401
                            then
                              let uu____21402 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21402 with
                              | uu____21447::(FStar_Pervasives_Native.Some
                                              (true ),uu____21448)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21499)::uu____21500::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21551)::(uu____21552,(arg,uu____21554))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21603,(p,uu____21605))::(uu____21606,
                                                                (q,uu____21608))::[]
                                  ->
                                  let uu____21655 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21655
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21657 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21671 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21671
                               then
                                 let uu____21672 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21672 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21717)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21718)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21769)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21770)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21821)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21822)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21873)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21874)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21925,(arg,uu____21927))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21928)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21977)::(uu____21978,(arg,uu____21980))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22029,(arg,uu____22031))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22032)::[]
                                     ->
                                     let uu____22081 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22081
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22082)::(uu____22083,(arg,uu____22085))::[]
                                     ->
                                     let uu____22134 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22134
                                 | (uu____22135,(p,uu____22137))::(uu____22138,
                                                                   (q,uu____22140))::[]
                                     ->
                                     let uu____22187 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22187
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22189 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22203 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22203
                                  then
                                    let uu____22204 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22204 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22249)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22280)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22311 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22325 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22325
                                     then
                                       match args with
                                       | (t,uu____22327)::[] ->
                                           let uu____22344 =
                                             let uu____22345 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22345.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22344 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22348::[],body,uu____22350)
                                                ->
                                                let uu____22377 = simp_t body
                                                   in
                                                (match uu____22377 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22380 -> tm1)
                                            | uu____22383 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22385))::(t,uu____22387)::[]
                                           ->
                                           let uu____22414 =
                                             let uu____22415 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22415.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22414 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22418::[],body,uu____22420)
                                                ->
                                                let uu____22447 = simp_t body
                                                   in
                                                (match uu____22447 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22450 -> tm1)
                                            | uu____22453 -> tm1)
                                       | uu____22454 -> tm1
                                     else
                                       (let uu____22464 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22464
                                        then
                                          match args with
                                          | (t,uu____22466)::[] ->
                                              let uu____22483 =
                                                let uu____22484 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22484.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22483 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22487::[],body,uu____22489)
                                                   ->
                                                   let uu____22516 =
                                                     simp_t body  in
                                                   (match uu____22516 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22519 -> tm1)
                                               | uu____22522 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22524))::(t,uu____22526)::[]
                                              ->
                                              let uu____22553 =
                                                let uu____22554 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22554.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22553 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22557::[],body,uu____22559)
                                                   ->
                                                   let uu____22586 =
                                                     simp_t body  in
                                                   (match uu____22586 with
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
                                                    | uu____22589 -> tm1)
                                               | uu____22592 -> tm1)
                                          | uu____22593 -> tm1
                                        else
                                          (let uu____22603 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22603
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22604;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22605;_},uu____22606)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22623;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22624;_},uu____22625)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22642 -> tm1
                                           else
                                             (let uu____22652 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22652 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22672 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22687 = simp_t t  in
                      (match uu____22687 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22690 ->
                      let uu____22713 = is_const_match tm1  in
                      (match uu____22713 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22716 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22726  ->
               (let uu____22728 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22729 = FStar_Syntax_Print.term_to_string t  in
                let uu____22730 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22737 =
                  let uu____22738 =
                    let uu____22741 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22741
                     in
                  stack_to_string uu____22738  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22728 uu____22729 uu____22730 uu____22737);
               (let uu____22764 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22764
                then
                  let uu____22765 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22765 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22772 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22773 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22774 =
                          let uu____22775 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22775
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22772
                          uu____22773 uu____22774);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22793 =
                     let uu____22794 =
                       let uu____22795 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22795  in
                     FStar_Util.string_of_int uu____22794  in
                   let uu____22800 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22801 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22793 uu____22800 uu____22801)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22807,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22858  ->
                     let uu____22859 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22859);
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
               let uu____22897 =
                 let uu___210_22898 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___210_22898.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___210_22898.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22897
           | (Arg (Univ uu____22901,uu____22902,uu____22903))::uu____22904 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22907,uu____22908))::uu____22909 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22924,uu____22925),aq,r))::stack1
               when
               let uu____22975 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22975 ->
               let t2 =
                 let uu____22979 =
                   let uu____22984 =
                     let uu____22985 = closure_as_term cfg env_arg tm  in
                     (uu____22985, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22984  in
                 uu____22979 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22995),aq,r))::stack1 ->
               (log cfg
                  (fun uu____23048  ->
                     let uu____23049 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____23049);
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
                  (let uu____23061 = FStar_ST.op_Bang m  in
                   match uu____23061 with
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
                   | FStar_Pervasives_Native.Some (uu____23204,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23257 =
                 log cfg
                   (fun uu____23261  ->
                      let uu____23262 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23262);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23268 =
                 let uu____23269 = FStar_Syntax_Subst.compress t1  in
                 uu____23269.FStar_Syntax_Syntax.n  in
               (match uu____23268 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23296 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23296  in
                    (log cfg
                       (fun uu____23300  ->
                          let uu____23301 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23301);
                     (let uu____23302 = FStar_List.tl stack  in
                      norm cfg env1 uu____23302 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23303);
                       FStar_Syntax_Syntax.pos = uu____23304;
                       FStar_Syntax_Syntax.vars = uu____23305;_},(e,uu____23307)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23336 when
                    (cfg.steps).primops ->
                    let uu____23351 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23351 with
                     | (hd1,args) ->
                         let uu____23388 =
                           let uu____23389 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23389.FStar_Syntax_Syntax.n  in
                         (match uu____23388 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23393 = find_prim_step cfg fv  in
                              (match uu____23393 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23396; arity = uu____23397;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23399;
                                     requires_binder_substitution =
                                       uu____23400;
                                     interpretation = uu____23401;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23417 -> fallback " (3)" ())
                          | uu____23420 -> fallback " (4)" ()))
                | uu____23421 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23444  ->
                     let uu____23445 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23445);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23454 =
                   log cfg1
                     (fun uu____23459  ->
                        let uu____23460 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23461 =
                          let uu____23462 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23489  ->
                                    match uu____23489 with
                                    | (p,uu____23499,uu____23500) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23462
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23460 uu____23461);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___119_23517  ->
                                match uu___119_23517 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23518 -> false))
                         in
                      let steps =
                        let uu___211_23520 = cfg1.steps  in
                        {
                          beta = (uu___211_23520.beta);
                          iota = (uu___211_23520.iota);
                          zeta = false;
                          weak = (uu___211_23520.weak);
                          hnf = (uu___211_23520.hnf);
                          primops = (uu___211_23520.primops);
                          do_not_unfold_pure_lets =
                            (uu___211_23520.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___211_23520.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___211_23520.pure_subterms_within_computations);
                          simplify = (uu___211_23520.simplify);
                          erase_universes = (uu___211_23520.erase_universes);
                          allow_unbound_universes =
                            (uu___211_23520.allow_unbound_universes);
                          reify_ = (uu___211_23520.reify_);
                          compress_uvars = (uu___211_23520.compress_uvars);
                          no_full_norm = (uu___211_23520.no_full_norm);
                          check_no_uvars = (uu___211_23520.check_no_uvars);
                          unmeta = (uu___211_23520.unmeta);
                          unascribe = (uu___211_23520.unascribe);
                          in_full_norm_request =
                            (uu___211_23520.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___211_23520.weakly_reduce_scrutinee)
                        }  in
                      let uu___212_23525 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___212_23525.tcenv);
                        debug = (uu___212_23525.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___212_23525.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___212_23525.memoize_lazy);
                        normalize_pure_lets =
                          (uu___212_23525.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23597 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23626 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23710  ->
                                    fun uu____23711  ->
                                      match (uu____23710, uu____23711) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23850 = norm_pat env3 p1
                                             in
                                          (match uu____23850 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23626 with
                           | (pats1,env3) ->
                               ((let uu___213_24012 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___213_24012.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___214_24031 = x  in
                            let uu____24032 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___214_24031.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___214_24031.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24032
                            }  in
                          ((let uu___215_24046 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___215_24046.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___216_24057 = x  in
                            let uu____24058 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___216_24057.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___216_24057.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24058
                            }  in
                          ((let uu___217_24072 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___217_24072.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___218_24088 = x  in
                            let uu____24089 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___218_24088.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___218_24088.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24089
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___219_24104 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___219_24104.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24148 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24164 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24164 with
                                  | (p,wopt,e) ->
                                      let uu____24184 = norm_pat env1 p  in
                                      (match uu____24184 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24239 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24239
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24252 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24252
                      then
                        norm
                          (let uu___220_24257 = cfg1  in
                           {
                             steps =
                               (let uu___221_24260 = cfg1.steps  in
                                {
                                  beta = (uu___221_24260.beta);
                                  iota = (uu___221_24260.iota);
                                  zeta = (uu___221_24260.zeta);
                                  weak = (uu___221_24260.weak);
                                  hnf = (uu___221_24260.hnf);
                                  primops = (uu___221_24260.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___221_24260.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___221_24260.unfold_until);
                                  unfold_only = (uu___221_24260.unfold_only);
                                  unfold_fully =
                                    (uu___221_24260.unfold_fully);
                                  unfold_attr = (uu___221_24260.unfold_attr);
                                  unfold_tac = (uu___221_24260.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___221_24260.pure_subterms_within_computations);
                                  simplify = (uu___221_24260.simplify);
                                  erase_universes =
                                    (uu___221_24260.erase_universes);
                                  allow_unbound_universes =
                                    (uu___221_24260.allow_unbound_universes);
                                  reify_ = (uu___221_24260.reify_);
                                  compress_uvars =
                                    (uu___221_24260.compress_uvars);
                                  no_full_norm =
                                    (uu___221_24260.no_full_norm);
                                  check_no_uvars =
                                    (uu___221_24260.check_no_uvars);
                                  unmeta = (uu___221_24260.unmeta);
                                  unascribe = (uu___221_24260.unascribe);
                                  in_full_norm_request =
                                    (uu___221_24260.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___220_24257.tcenv);
                             debug = (uu___220_24257.debug);
                             delta_level = (uu___220_24257.delta_level);
                             primitive_steps =
                               (uu___220_24257.primitive_steps);
                             strong = (uu___220_24257.strong);
                             memoize_lazy = (uu___220_24257.memoize_lazy);
                             normalize_pure_lets =
                               (uu___220_24257.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24262 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24262)
                    in
                 let rec is_cons head1 =
                   let uu____24287 =
                     let uu____24288 = FStar_Syntax_Subst.compress head1  in
                     uu____24288.FStar_Syntax_Syntax.n  in
                   match uu____24287 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24292) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24297 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24298;
                         FStar_Syntax_Syntax.fv_delta = uu____24299;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24300;
                         FStar_Syntax_Syntax.fv_delta = uu____24301;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24302);_}
                       -> true
                   | uu____24309 -> false  in
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
                   let uu____24472 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24472 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24559 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24598 ->
                                 let uu____24599 =
                                   let uu____24600 = is_cons head1  in
                                   Prims.op_Negation uu____24600  in
                                 FStar_Util.Inr uu____24599)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24625 =
                              let uu____24626 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24626.FStar_Syntax_Syntax.n  in
                            (match uu____24625 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____24644 ->
                                 let uu____24645 =
                                   let uu____24646 = is_cons head1  in
                                   Prims.op_Negation uu____24646  in
                                 FStar_Util.Inr uu____24645))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24723)::rest_a,(p1,uu____24726)::rest_p) ->
                       let uu____24770 = matches_pat t2 p1  in
                       (match uu____24770 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24819 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24937 = matches_pat scrutinee1 p1  in
                       (match uu____24937 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24977  ->
                                  let uu____24978 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24979 =
                                    let uu____24980 =
                                      FStar_List.map
                                        (fun uu____24990  ->
                                           match uu____24990 with
                                           | (uu____24995,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24980
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24978 uu____24979);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____25027  ->
                                       match uu____25027 with
                                       | (bv,t2) ->
                                           let uu____25050 =
                                             let uu____25057 =
                                               let uu____25060 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____25060
                                                in
                                             let uu____25061 =
                                               let uu____25062 =
                                                 let uu____25093 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____25093, false)
                                                  in
                                               Clos uu____25062  in
                                             (uu____25057, uu____25061)  in
                                           uu____25050 :: env2) env1 s
                                 in
                              let uu____25206 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25206)))
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
    let uu____25233 =
      let uu____25236 = FStar_ST.op_Bang plugins  in p :: uu____25236  in
    FStar_ST.op_Colon_Equals plugins uu____25233  in
  let retrieve uu____25344 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25421  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___120_25462  ->
                  match uu___120_25462 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25466 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25472 -> d  in
        let uu____25475 = to_fsteps s  in
        let uu____25476 =
          let uu____25477 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25478 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25479 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25480 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____25481 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25482 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25477;
            primop = uu____25478;
            b380 = uu____25479;
            wpe = uu____25480;
            norm_delayed = uu____25481;
            print_normalized = uu____25482
          }  in
        let uu____25483 =
          let uu____25486 =
            let uu____25489 = retrieve_plugins ()  in
            FStar_List.append uu____25489 psteps  in
          add_steps built_in_primitive_steps uu____25486  in
        let uu____25492 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25494 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25494)
           in
        {
          steps = uu____25475;
          tcenv = e;
          debug = uu____25476;
          delta_level = d1;
          primitive_steps = uu____25483;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25492
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
      fun t  -> let uu____25576 = config s e  in norm_comp uu____25576 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25593 = config [] env  in norm_universe uu____25593 [] u
  
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
        let uu____25617 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25617  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25624 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___222_25643 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___222_25643.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___222_25643.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25650 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25650
          then
            let ct1 =
              let uu____25652 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25652 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____25659 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25659
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___223_25663 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___223_25663.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___223_25663.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___223_25663.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___224_25665 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___224_25665.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___224_25665.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___224_25665.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___224_25665.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___225_25666 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___225_25666.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___225_25666.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25668 -> c
  
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
        let uu____25686 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25686  in
      let uu____25693 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25693
      then
        let uu____25694 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25694 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25700  ->
                 let uu____25701 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25701)
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
            ((let uu____25722 =
                let uu____25727 =
                  let uu____25728 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25728
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25727)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25722);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25743 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25743 [] c
        with
        | e ->
            ((let uu____25756 =
                let uu____25761 =
                  let uu____25762 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25762
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25761)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25756);
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
                   let uu____25807 =
                     let uu____25808 =
                       let uu____25815 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25815)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25808  in
                   mk uu____25807 t01.FStar_Syntax_Syntax.pos
               | uu____25820 -> t2)
          | uu____25821 -> t2  in
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
        let uu____25885 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25885 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25914 ->
                 let uu____25921 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25921 with
                  | (actuals,uu____25931,uu____25932) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25946 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25946 with
                         | (binders,args) ->
                             let uu____25957 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25957
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
      | uu____25971 ->
          let uu____25972 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25972 with
           | (head1,args) ->
               let uu____26009 =
                 let uu____26010 = FStar_Syntax_Subst.compress head1  in
                 uu____26010.FStar_Syntax_Syntax.n  in
               (match uu____26009 with
                | FStar_Syntax_Syntax.Tm_uvar u ->
                    let uu____26014 =
                      FStar_Syntax_Util.arrow_formals
                        u.FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    (match uu____26014 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26056 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___230_26064 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___230_26064.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___230_26064.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___230_26064.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___230_26064.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___230_26064.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___230_26064.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___230_26064.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___230_26064.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___230_26064.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___230_26064.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___230_26064.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___230_26064.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___230_26064.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___230_26064.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___230_26064.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___230_26064.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___230_26064.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___230_26064.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___230_26064.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___230_26064.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___230_26064.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___230_26064.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___230_26064.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___230_26064.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___230_26064.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___230_26064.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___230_26064.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___230_26064.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___230_26064.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___230_26064.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___230_26064.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___230_26064.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___230_26064.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___230_26064.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___230_26064.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____26056 with
                            | (uu____26065,ty,uu____26067) ->
                                eta_expand_with_type env t ty))
                | uu____26068 ->
                    let uu____26069 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___231_26077 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___231_26077.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___231_26077.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___231_26077.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___231_26077.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___231_26077.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___231_26077.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___231_26077.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___231_26077.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___231_26077.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___231_26077.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___231_26077.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___231_26077.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___231_26077.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___231_26077.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___231_26077.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___231_26077.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___231_26077.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___231_26077.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___231_26077.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___231_26077.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___231_26077.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___231_26077.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___231_26077.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___231_26077.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___231_26077.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___231_26077.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___231_26077.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___231_26077.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___231_26077.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___231_26077.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___231_26077.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___231_26077.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___231_26077.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___231_26077.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___231_26077.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____26069 with
                     | (uu____26078,ty,uu____26080) ->
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
      let uu___232_26153 = x  in
      let uu____26154 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___232_26153.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___232_26153.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26154
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26157 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26182 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26183 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26184 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26185 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26192 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26193 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26194 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___233_26224 = rc  in
          let uu____26225 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26234 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___233_26224.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26225;
            FStar_Syntax_Syntax.residual_flags = uu____26234
          }  in
        let uu____26237 =
          let uu____26238 =
            let uu____26255 = elim_delayed_subst_binders bs  in
            let uu____26262 = elim_delayed_subst_term t2  in
            let uu____26265 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26255, uu____26262, uu____26265)  in
          FStar_Syntax_Syntax.Tm_abs uu____26238  in
        mk1 uu____26237
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26296 =
          let uu____26297 =
            let uu____26310 = elim_delayed_subst_binders bs  in
            let uu____26317 = elim_delayed_subst_comp c  in
            (uu____26310, uu____26317)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26297  in
        mk1 uu____26296
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26334 =
          let uu____26335 =
            let uu____26342 = elim_bv bv  in
            let uu____26343 = elim_delayed_subst_term phi  in
            (uu____26342, uu____26343)  in
          FStar_Syntax_Syntax.Tm_refine uu____26335  in
        mk1 uu____26334
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26370 =
          let uu____26371 =
            let uu____26386 = elim_delayed_subst_term t2  in
            let uu____26389 = elim_delayed_subst_args args  in
            (uu____26386, uu____26389)  in
          FStar_Syntax_Syntax.Tm_app uu____26371  in
        mk1 uu____26370
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___234_26457 = p  in
              let uu____26458 =
                let uu____26459 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26459  in
              {
                FStar_Syntax_Syntax.v = uu____26458;
                FStar_Syntax_Syntax.p =
                  (uu___234_26457.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___235_26461 = p  in
              let uu____26462 =
                let uu____26463 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26463  in
              {
                FStar_Syntax_Syntax.v = uu____26462;
                FStar_Syntax_Syntax.p =
                  (uu___235_26461.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___236_26470 = p  in
              let uu____26471 =
                let uu____26472 =
                  let uu____26479 = elim_bv x  in
                  let uu____26480 = elim_delayed_subst_term t0  in
                  (uu____26479, uu____26480)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26472  in
              {
                FStar_Syntax_Syntax.v = uu____26471;
                FStar_Syntax_Syntax.p =
                  (uu___236_26470.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___237_26503 = p  in
              let uu____26504 =
                let uu____26505 =
                  let uu____26518 =
                    FStar_List.map
                      (fun uu____26541  ->
                         match uu____26541 with
                         | (x,b) ->
                             let uu____26554 = elim_pat x  in
                             (uu____26554, b)) pats
                     in
                  (fv, uu____26518)  in
                FStar_Syntax_Syntax.Pat_cons uu____26505  in
              {
                FStar_Syntax_Syntax.v = uu____26504;
                FStar_Syntax_Syntax.p =
                  (uu___237_26503.FStar_Syntax_Syntax.p)
              }
          | uu____26567 -> p  in
        let elim_branch uu____26591 =
          match uu____26591 with
          | (pat,wopt,t3) ->
              let uu____26617 = elim_pat pat  in
              let uu____26620 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____26623 = elim_delayed_subst_term t3  in
              (uu____26617, uu____26620, uu____26623)
           in
        let uu____26628 =
          let uu____26629 =
            let uu____26652 = elim_delayed_subst_term t2  in
            let uu____26655 = FStar_List.map elim_branch branches  in
            (uu____26652, uu____26655)  in
          FStar_Syntax_Syntax.Tm_match uu____26629  in
        mk1 uu____26628
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26786 =
          match uu____26786 with
          | (tc,topt) ->
              let uu____26821 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26831 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26831
                | FStar_Util.Inr c ->
                    let uu____26833 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26833
                 in
              let uu____26834 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26821, uu____26834)
           in
        let uu____26843 =
          let uu____26844 =
            let uu____26871 = elim_delayed_subst_term t2  in
            let uu____26874 = elim_ascription a  in
            (uu____26871, uu____26874, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26844  in
        mk1 uu____26843
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___238_26935 = lb  in
          let uu____26936 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26939 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___238_26935.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___238_26935.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26936;
            FStar_Syntax_Syntax.lbeff =
              (uu___238_26935.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26939;
            FStar_Syntax_Syntax.lbattrs =
              (uu___238_26935.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___238_26935.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26942 =
          let uu____26943 =
            let uu____26956 =
              let uu____26963 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26963)  in
            let uu____26972 = elim_delayed_subst_term t2  in
            (uu____26956, uu____26972)  in
          FStar_Syntax_Syntax.Tm_let uu____26943  in
        mk1 uu____26942
    | FStar_Syntax_Syntax.Tm_uvar u -> mk1 (FStar_Syntax_Syntax.Tm_uvar u)
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26991 =
          let uu____26992 =
            let uu____26999 = elim_delayed_subst_term tm  in
            (uu____26999, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26992  in
        mk1 uu____26991
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27010 =
          let uu____27011 =
            let uu____27018 = elim_delayed_subst_term t2  in
            let uu____27021 = elim_delayed_subst_meta md  in
            (uu____27018, uu____27021)  in
          FStar_Syntax_Syntax.Tm_meta uu____27011  in
        mk1 uu____27010

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___121_27030  ->
         match uu___121_27030 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27034 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27034
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
        let uu____27057 =
          let uu____27058 =
            let uu____27067 = elim_delayed_subst_term t  in
            (uu____27067, uopt)  in
          FStar_Syntax_Syntax.Total uu____27058  in
        mk1 uu____27057
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27084 =
          let uu____27085 =
            let uu____27094 = elim_delayed_subst_term t  in
            (uu____27094, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27085  in
        mk1 uu____27084
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___239_27103 = ct  in
          let uu____27104 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27107 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27116 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___239_27103.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___239_27103.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27104;
            FStar_Syntax_Syntax.effect_args = uu____27107;
            FStar_Syntax_Syntax.flags = uu____27116
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___122_27119  ->
    match uu___122_27119 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____27131 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____27131
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27164 =
          let uu____27171 = elim_delayed_subst_term t  in (m, uu____27171)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27164
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27183 =
          let uu____27192 = elim_delayed_subst_term t  in
          (m1, m2, uu____27192)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27183
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27219  ->
         match uu____27219 with
         | (t,q) ->
             let uu____27230 = elim_delayed_subst_term t  in (uu____27230, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27250  ->
         match uu____27250 with
         | (x,q) ->
             let uu____27261 =
               let uu___240_27262 = x  in
               let uu____27263 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___240_27262.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___240_27262.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27263
               }  in
             (uu____27261, q)) bs

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
            | (uu____27355,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27381,FStar_Util.Inl t) ->
                let uu____27399 =
                  let uu____27406 =
                    let uu____27407 =
                      let uu____27420 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27420)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27407  in
                  FStar_Syntax_Syntax.mk uu____27406  in
                uu____27399 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27434 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27434 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27464 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27527 ->
                    let uu____27528 =
                      let uu____27537 =
                        let uu____27538 = FStar_Syntax_Subst.compress t4  in
                        uu____27538.FStar_Syntax_Syntax.n  in
                      (uu____27537, tc)  in
                    (match uu____27528 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27565) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____27606) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27645,FStar_Util.Inl uu____27646) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27669 -> failwith "Impossible")
                 in
              (match uu____27464 with
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
          let uu____27794 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____27794 with
          | (univ_names1,binders1,tc) ->
              let uu____27860 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____27860)
  
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
          let uu____27909 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____27909 with
          | (univ_names1,binders1,tc) ->
              let uu____27975 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27975)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28014 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28014 with
           | (univ_names1,binders1,typ1) ->
               let uu___241_28048 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___241_28048.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___241_28048.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___241_28048.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___241_28048.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___242_28063 = s  in
          let uu____28064 =
            let uu____28065 =
              let uu____28074 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28074, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28065  in
          {
            FStar_Syntax_Syntax.sigel = uu____28064;
            FStar_Syntax_Syntax.sigrng =
              (uu___242_28063.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___242_28063.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___242_28063.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___242_28063.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28091 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28091 with
           | (univ_names1,uu____28111,typ1) ->
               let uu___243_28129 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___243_28129.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___243_28129.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___243_28129.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___243_28129.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28135 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28135 with
           | (univ_names1,uu____28155,typ1) ->
               let uu___244_28173 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___244_28173.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___244_28173.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___244_28173.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___244_28173.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28201 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28201 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28226 =
                            let uu____28227 =
                              let uu____28228 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28228  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28227
                             in
                          elim_delayed_subst_term uu____28226  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___245_28231 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___245_28231.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___245_28231.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___245_28231.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___245_28231.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___246_28232 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___246_28232.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_28232.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_28232.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_28232.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___247_28238 = s  in
          let uu____28239 =
            let uu____28240 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28240  in
          {
            FStar_Syntax_Syntax.sigel = uu____28239;
            FStar_Syntax_Syntax.sigrng =
              (uu___247_28238.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___247_28238.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___247_28238.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___247_28238.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28244 = elim_uvars_aux_t env us [] t  in
          (match uu____28244 with
           | (us1,uu____28264,t1) ->
               let uu___248_28282 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_28282.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_28282.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_28282.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_28282.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28283 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28285 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28285 with
           | (univs1,binders,signature) ->
               let uu____28319 =
                 let uu____28328 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28328 with
                 | (univs_opening,univs2) ->
                     let uu____28355 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28355)
                  in
               (match uu____28319 with
                | (univs_opening,univs_closing) ->
                    let uu____28372 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28378 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28379 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28378, uu____28379)  in
                    (match uu____28372 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28403 =
                           match uu____28403 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28421 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28421 with
                                | (us1,t1) ->
                                    let uu____28432 =
                                      let uu____28441 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28450 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28441, uu____28450)  in
                                    (match uu____28432 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28477 =
                                           let uu____28486 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28495 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28486, uu____28495)  in
                                         (match uu____28477 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28523 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28523
                                                 in
                                              let uu____28524 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28524 with
                                               | (uu____28547,uu____28548,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28567 =
                                                       let uu____28568 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28568
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28567
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28577 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28577 with
                           | (uu____28594,uu____28595,t1) -> t1  in
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
                             | uu____28669 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____28694 =
                               let uu____28695 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____28695.FStar_Syntax_Syntax.n  in
                             match uu____28694 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____28754 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____28785 =
                               let uu____28786 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____28786.FStar_Syntax_Syntax.n  in
                             match uu____28785 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____28807) ->
                                 let uu____28828 = destruct_action_body body
                                    in
                                 (match uu____28828 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____28873 ->
                                 let uu____28874 = destruct_action_body t  in
                                 (match uu____28874 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____28923 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____28923 with
                           | (action_univs,t) ->
                               let uu____28932 = destruct_action_typ_templ t
                                  in
                               (match uu____28932 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___249_28973 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___249_28973.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___249_28973.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___250_28975 = ed  in
                           let uu____28976 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____28977 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____28978 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____28979 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____28980 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____28981 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____28982 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____28983 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____28984 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____28985 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____28986 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____28987 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____28988 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____28989 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___250_28975.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___250_28975.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____28976;
                             FStar_Syntax_Syntax.bind_wp = uu____28977;
                             FStar_Syntax_Syntax.if_then_else = uu____28978;
                             FStar_Syntax_Syntax.ite_wp = uu____28979;
                             FStar_Syntax_Syntax.stronger = uu____28980;
                             FStar_Syntax_Syntax.close_wp = uu____28981;
                             FStar_Syntax_Syntax.assert_p = uu____28982;
                             FStar_Syntax_Syntax.assume_p = uu____28983;
                             FStar_Syntax_Syntax.null_wp = uu____28984;
                             FStar_Syntax_Syntax.trivial = uu____28985;
                             FStar_Syntax_Syntax.repr = uu____28986;
                             FStar_Syntax_Syntax.return_repr = uu____28987;
                             FStar_Syntax_Syntax.bind_repr = uu____28988;
                             FStar_Syntax_Syntax.actions = uu____28989;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___250_28975.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___251_28992 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___251_28992.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___251_28992.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___251_28992.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___251_28992.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___123_29013 =
            match uu___123_29013 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29044 = elim_uvars_aux_t env us [] t  in
                (match uu____29044 with
                 | (us1,uu____29072,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___252_29099 = sub_eff  in
            let uu____29100 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29103 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___252_29099.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___252_29099.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29100;
              FStar_Syntax_Syntax.lift = uu____29103
            }  in
          let uu___253_29106 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___253_29106.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___253_29106.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___253_29106.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___253_29106.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____29116 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29116 with
           | (univ_names1,binders1,comp1) ->
               let uu___254_29150 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___254_29150.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___254_29150.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___254_29150.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___254_29150.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29153 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29154 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  